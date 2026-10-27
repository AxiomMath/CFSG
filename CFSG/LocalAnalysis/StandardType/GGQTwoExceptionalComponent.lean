module

public import CFSG.LocalAnalysis.StandardType.GGQTwoExceptionalRealization
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavQuotient
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust
public import CFSG.LocalAnalysis.StandardType.GGQTwoRationalComponent
public import CFSG.LocalAnalysis.StandardType.GGQTwoF4RationalAutomizer
public import CFSG.LocalAnalysis.StandardType.GGLangUniform
public import CFSG.LocalAnalysis.StandardType.GGQTwoCavMarking
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.AlgSetupUntw
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtUntw
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerTwRigidSplit
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerFivePairRigid
public import CFSG.HardMathSupport.Dickson.Sec6.Up34Chev2Aux.InnExcEmb

public noncomputable section

namespace CFSG.StandardType.QTwoCav

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.HardMathSupport.Dickson.Sec6.Up34Exc
  CFSG.HardMathSupport.Solomon.Coordinator



theorem actual_langSetup_of_exceptional_datum {G : Type} [Group G]
    {Bs L : Subgroup G} {K : Type} [Field K] [Finite K] {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E7 ∨ τ = .E8) (hK : Nat.card K = 2)
    (θ : L ⧸ Subgroup.center L ≃* adjointGroup τ K)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hI : (ggBeta L θ hN).range ≤
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)).range)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ 2)
    (D : LangDatum τ (AlgebraicClosure K)) (w : WeylGroup τ)
    (hDΦ : D.Φ = Units.map (entrywiseHom Fr)) (hDq : D.q = 2)
    (hDn : D.n = canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
    (hneg : ∀ u : Fin τ.rank → ℤ, w • u = -u)
    (htor : ∀ y : ModGL τ (AlgebraicClosure K), (y ∈ D.torus ∧ y ^ 3 = 1) ↔
      ∃ x ∈ exceptionalImage θ hN,
        D.g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL τ K) * D.g0 = y) :
    ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
      (ι : adjointGroup τ K →* ModGL τ (AlgebraicClosure K)),
      S.D = D ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot τ γ → S.ρ γ = -γ) ∧
      Function.Injective ι ∧ ι.range = S.Γ ∧
      (∀ c : adjointGroup τ K, ι c = D.g0⁻¹ *
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL τ K) * D.g0) ∧
      (∀ u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom,
        ∃ a : Fin τ.rank → (AlgebraicClosure K)ˣ,
          rootDiagUnit τ a ∈ S.D.torus ∧ rootDiagUnit τ a = D.g0⁻¹ * u * D.g0 ∧
          ∀ β : MulAut (adjointGroup τ K),
            (∀ c, ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
              (adjointGroup τ K).subtype) (β c) =
                u * ((baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
                  (adjointGroup τ K).subtype) c * u⁻¹) →
            ∀ c, ι (β c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹) ∧
      fullThreeTorus S = (exceptionalImage θ hN).map ι := by
  classical
  let Ω := AlgebraicClosure K
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK]; norm_num)
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let ι₀ : adjointGroup τ K →* ModGL τ Ω :=
    (baseChangeGL (algebraMap K Ω)).comp (adjointGroup τ K).subtype
  have hι₀ : Function.Injective ι₀ :=
    (baseChangeGL_injective (algebraMap K Ω)).comp (Subgroup.subtype_injective _)
  have hFrCard : ∀ c, Fr c = c ^ Nat.card K := by
    rw [hK]
    exact hFr
  have hperf : commutator ↥(adjointGroup τ K) = ⊤ := by
    rcases hτ with rfl | rfl | rfl
    · exact commutator_adjointGroup_F4_eq_top K
    · exact commutator_adjointGroup_E7_eq_top K
    · exact commutator_adjointGroup_E8_eq_top K
  have hd : LangDescent D 5 ι₀ := by
    rcases hτ with rfl | rfl | rfl
    · exact langDescent_exact (Or.inr rfl) hFrCard D hDΦ hperf
    · exact langDescent_untw 2 (Or.inr (Or.inl ⟨rfl, rfl⟩)) hFrCard D hDΦ
        Nat.prime_five (by norm_num) hperf
    · exact langDescent_untw 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) hFrCard D hDΦ
        Nat.prime_five (by norm_num) hperf
  have hfin : Finite D.model := hd.finite_model
  have hΓ : D.Γ = ι₀.range.map (MulAut.conj D.g0⁻¹).toMonoidHom := hd.Γ_eq
  obtain ⟨S, ι, hSD, hιval, hιinj, hιrange, huniform⟩ :=
    LangRat.exists_langSetup_of_toral_datum_uniform (τ := τ) (L := Ω) (ℓ := 2) (f := 1)
      Nat.prime_two le_rfl D (by rw [hDq]; norm_num)
      Nat.prime_five (by norm_num) (Or.inl le_rfl) hfin ι₀ hι₀ hΓ
  have hqS : S.D.q = 2 := by rw [hSD, hDq]
  have hAlg : S.IsAlgebraic :=
    S.isAlgebraic_of_isAlgClosure K 1 (by rw [pow_one, hqS, hK])
  have hρS : ∀ γ, IsRoot τ γ → S.ρ γ = -γ := by
    intro γ hγ
    have hfrobD : FrobRootMap D S.ρ := by
      rw [← hSD]
      exact S.frob
    let D' : LangDatum τ Ω := LangDatum.ofFrobenius Fr 2 hFr w D.g0_mem
      (by rw [← hDΦ, ← hDn]; exact D.lang)
    have hfrobD' : FrobRootMap D' S.ρ :=
      frobRootMap_congr_fields hDΦ.symm hDq.symm hDn.symm hfrobD
    have h := frobRootMap_ofFrobenius_apply (τ := τ) (L := Ω) (Fr := Fr) (q := 2)
      (by norm_num) hFr D.g0_mem (hg0 := by rw [← hDΦ, ← hDn]; exact D.lang) hfrobD' hγ
    rw [h, hneg γ]
  have htorEq : S.D.torus = (exceptionalImage θ hN).map ι := by
    rw [hSD]
    ext y
    constructor
    · intro hy
      have hyS : y ∈ S.D.torus := by rwa [hSD]
      have hmem : y ∈ fullThreeTorus S := by
        rwa [fullThreeTorus_eq_torus S hqS hρS]
      have hy3 : y ^ 3 = 1 := ((mem_fullThreeTorus S).1 hmem).2
      obtain ⟨x, hx, hxy⟩ := (htor y).1 ⟨hy, hy3⟩
      exact ⟨x, hx, (hιval x).trans hxy⟩
    · rintro ⟨x, hx, rfl⟩
      have hy := (htor (ι x)).2 ⟨x, hx, (hιval x).symm⟩
      exact hy.1
  have hfull : fullThreeTorus S = (exceptionalImage θ hN).map ι := by
    rw [fullThreeTorus_eq_torus S hqS hρS, htorEq]
  exact ⟨S, ι, hSD, hAlg, hρS, hιinj, hιrange, hιval, huniform, hfull⟩

theorem exists_rationalComponent_of_full_marking {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab)
    (htag : lab.tag = .F4 ∨ lab.tag = .E7 ∨ lab.tag = .E8)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ GGQ2LieRank lab)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    ∃ (τ : Tag) (K : Type) (hfield : Field K), letI := hfield;
      ∃ (hfinite : Finite K), letI := hfinite;
        ∃ (S : LangSetup τ (AlgebraicClosure K) 5)
          (a : Fin τ.rank → (AlgebraicClosure K)ˣ)
          (i : KernelComponent (rootCharHom a)),
          (τ = .F4 ∨ τ = .E7 ∨ τ = .E8) ∧ τ.rank = GGQ2LieRank lab ∧
          S.D.q = 2 ∧ S.IsAlgebraic ∧ (∀ γ, IsRoot τ γ → S.ρ γ = -γ) ∧
          rootDiagUnit τ a ∈ S.D.torus ∧ (∀ j, a j ^ 3 = 1) ∧ rootDiagUnit τ a ≠ 1 ∧
          CFSG.IsQuasisimple ↥(rationalComponent S.ρ S.Γ (rootCharHom a) i) ∧
          Nat.card (ggAutomizer ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
            (ggGamma L hN).range) =
            Nat.card (ggAutomizer (rationalComponent S.ρ S.Γ (rootCharHom a) i)
              (fullThreeTorus S)) := by
  classical
  have hBs3 : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  have hSS : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hL : commutator L = ⊤ := hSS.2.2.2.1.2.2.1
  obtain ⟨τ, K, instF, instFin, θ, hτ, hτrank, hK2, hI, hβEA, hβcard⟩ :=
    actual_beta_image_of_marking (hS := hS) (hp3 := rfl) (hq2 := hq2) (htag := htag)
      (hmark := hmark) (hN := hN) (e := GGQ2LieRank lab) hidx
  letI : Field K := instF
  letI : Finite K := instFin
  haveI : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK2]; norm_num)
  have hτF4 : τ = .F4 ∨ τ = .E7 ∨ τ = .E8 := hτ
  have hidxRank : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ τ.rank := by
    rw [hτrank]
    exact hidx
  obtain ⟨Fr, D, w, hFr, hDΦ, hDq, hDn, hneg, htor⟩ :=
    exceptional_full_lang hBs3 hL hτF4 hK2 θ hN hI hidxRank
  obtain ⟨S, ι, hSD, hAlg, hρS, hιinj, hιrange, hιval, huniform, hfull⟩ :=
    actual_langSetup_of_exceptional_datum hτF4 hK2 θ hN hI Fr hFr D w hDΦ hDq hDn hneg htor
  have hqS : S.D.q = 2 := by rw [hSD, hDq]
  let Ω := AlgebraicClosure K
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  let hDL := d_le_normalizer hS hN
  obtain ⟨d, hd1, -, hfixD⟩ :=
    exists_beta_d_generator θ Nat.prime_three hS hN
  let aD : MulAut (adjointGroup τ K) := ggBeta L θ hDL d
  have haDmem : aD ∈ (ggBeta L θ hN).range := by
    refine ⟨⟨d, ?_⟩, ?_⟩
    · exact hS.1.1.2.1.1 (hS.1.1.2.2.1.1 d.property)
    · ext z
      rfl
  obtain ⟨t, hta⟩ := hI haDmem
  have htexc : t ∈ exceptionalImage θ hN := by
    rw [exceptionalImage, Subgroup.mem_comap]
    rw [hta]
    exact haDmem
  obtain ⟨hImgEA, -⟩ := exceptionalImage_facts hBs3 hL θ hN hI
  have ht3 : t ^ 3 = 1 := hImgEA.2 t htexc
  have ht1 : t ≠ 1 := by
    intro h
    have haD1 : aD = 1 := by rw [← hta, h, map_one]
    exact hd1 haD1
  let u : ModGL τ Ω := baseChangeGL (algebraMap K Ω) (t : ModGL τ K)
  let y : ModGL τ Ω := D.g0⁻¹ * u * D.g0
  have hy : y ∈ D.torus ∧ y ^ 3 = 1 := (htor y).2 ⟨t, htexc, rfl⟩
  have hu : u ∈ D.torus.map (MulAut.conj D.g0).toMonoidHom := by
    refine ⟨y, hy.1, ?_⟩
    change D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹ = u
    group
  obtain ⟨a, haT, haeq, hact⟩ := huniform u hu
  have haeq' : rootDiagUnit τ a = y := by rw [haeq]
  have ha3 : ∀ i, a i ^ 3 = 1 := by
    have hroot3 : rootDiagUnit τ a ^ 3 = 1 := by rw [haeq']; exact hy.2
    have ha3' : a ^ 3 = 1 := by
      apply CFSG.LieType.Chevalley.rootDiagUnit_injective (τ := τ)
      simpa only [CFSG.LieType.Chevalley.rootDiagUnit_pow,
        CFSG.LieType.Chevalley.rootDiagUnit_one] using hroot3
    exact fun i => congrFun ha3' i
  have ha1 : rootDiagUnit τ a ≠ 1 := by
    intro h
    have hy1 : y = 1 := by rw [← haeq', h]
    have hu1 : u = 1 := by
      calc u = D.g0 * y * D.g0⁻¹ := by
            change u = D.g0 * (D.g0⁻¹ * u * D.g0) * D.g0⁻¹
            group
        _ = D.g0 * 1 * D.g0⁻¹ := by rw [hy1]
        _ = 1 := by group
    have hbase1 : baseChangeGL (algebraMap K Ω) (t : ModGL τ K) = 1 := by
      simpa [u] using hu1
    have hb : ((t : adjointGroup τ K) : ModGL τ K) = 1 :=
      CFSG.LieType.Chevalley.baseChangeGL_injective (τ := τ)
        (f := algebraMap K Ω) (a₁ := (t : ModGL τ K)) (a₂ := (1 : ModGL τ K))
        (by simpa using hbase1)
    exact ht1 (Subtype.ext hb)
  have hβconj : ∀ c : adjointGroup τ K,
      ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup τ K).subtype) ((MulAut.conj t) c) =
        u * ((baseChangeGL (algebraMap K Ω)).comp (adjointGroup τ K).subtype) c * u⁻¹ := by
    intro c
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    have hc : (((MulAut.conj t) c : adjointGroup τ K) : ModGL τ K) =
        (t : ModGL τ K) * (c : ModGL τ K) * (t : ModGL τ K)⁻¹ := rfl
    rw [hc, map_mul, map_mul, map_inv]
  have hact' : ∀ c : adjointGroup τ K,
      ι (aD c) = rootDiagUnit τ a * ι c * (rootDiagUnit τ a)⁻¹ := by
    intro c
    rw [show aD c = (MulAut.conj t) c by rw [← hta]]
    exact hact (MulAut.conj t) hβconj c
  let Kq : Subgroup (adjointGroup τ K) := (J.subgroupOf L).map (ggQuotHom θ)
  let B : Subgroup (adjointGroup τ K) := exceptionalImage θ hN
  have hcomp : CFSG.Open.IsComponentOf Kq (ggFix aD) := by
    have h := isComponentOf_quotient_image hDL θ hS.1.1.2.2.1.2.2.2.2.2.1
    rw [hfixD] at h
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open _ _).mp h
  have hfix : (ggFix aD).map ι = S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a} := by
    have h := map_fixSubgroup_eq_of_conj ι hιinj aD (rootDiagUnit τ a) hact'
    have hgg : ggFix aD = fixSubgroup aD := by
      ext c
      rfl
    rw [← hgg, hιrange] at h
    exact h
  have hcompΓ : CFSG.Open.IsComponentOf (Kq.map ι)
      (S.Γ ⊓ Subgroup.centralizer {rootDiagUnit τ a}) := by
    rw [← hfix]
    exact isComponentOf_map_inj hcomp ι hιinj
  have hpL : (3 : Ω) ≠ 0 := by
    have h2 : (2 : Ω) = 0 := CharP.cast_eq_zero Ω 2
    have h3 : (3 : Ω) = 1 := by
      calc (3 : Ω) = 2 + 1 := by norm_num
        _ = 1 := by rw [h2, zero_add]
    rw [h3]
    exact one_ne_zero
  obtain ⟨i, hQ, hi⟩ :=
    LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2 S
      (by rcases hτ with rfl | rfl | rfl <;> decide) Nat.prime_three hpL haT ha3 ha1 hcompΓ
  have hcardfull : Nat.card (ggAutomizer
      (rationalComponent S.ρ S.Γ (rootCharHom a) i) (fullThreeTorus S)) =
      Nat.card (ggAutomizer (Kq.map ι) (B.map ι)) := by
    rw [← hi]
    exact congrArg (fun T => Nat.card (ggAutomizer (Kq.map ι) T)) hfull
  have hcard1 : Nat.card (ggAutomizer (Kq.map ι) (B.map ι)) =
      Nat.card (ggAutomizer Kq B) := by
    rw [F4AutWeyl.ggAutomizer_map_eq hιinj Kq B rfl,
      Subgroup.card_map_of_injective (MulAut.congr _).injective]
  have hBmap : B.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) =
      (ggBeta L θ hN).range := by
    rw [show B = exceptionalImage θ hN from rfl, exceptionalImage,
      Subgroup.map_comap_eq_self hI]
  have hconj : Function.Injective
      (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)) :=
    mulAut_conj_injective (center_adjointGroup_eq_bot (τ := τ) (K := K))
  have hcard2 : Nat.card (ggAutomizer
      (Kq.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)))
      (ggBeta L θ hN).range) = Nat.card (ggAutomizer Kq B) := by
    calc Nat.card (ggAutomizer
          (Kq.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)))
          (ggBeta L θ hN).range)
        = Nat.card (ggAutomizer
            (Kq.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)))
            (B.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K)))) :=
          (congrArg (fun T => Nat.card (ggAutomizer
            (Kq.map (MulAut.conj : adjointGroup τ K →* MulAut (adjointGroup τ K))) T))
            hBmap).symm
      _ = Nat.card (ggAutomizer Kq B) := by
          rw [F4AutWeyl.ggAutomizer_map_eq hconj Kq B rfl,
            Subgroup.card_map_of_injective (MulAut.congr _).injective]
  have hcard3 := card_automizer_quotient_image_eq (J := J) θ hL hN
  refine ⟨τ, K, instF, instFin, S, a, i, hτ, hτrank, hqS, hAlg, hρS,
    haT, ha3, ha1, hQ, ?_⟩
  exact hcard3.symm.trans (hcard2.trans (hcard1.symm.trans hcardfull.symm))

theorem four_dvd_image_of_E7E8 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E7 ∨ lab.tag = .E8)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ GGQ2LieRank lab)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    4 ∣ Nat.card (ggAutomizer ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
      (ggGamma L hN).range) := by
  obtain ⟨τ, K, hfield, hfinite, S, a, i, hτRaw, hτrank, hq, hAlg, hρ,
    hT, ha3, h1, hQ, hcard⟩ :=
    exists_rationalComponent_of_full_marking hS hq2 (Or.inr htag) hmark hidx hN
  letI := hfield
  letI := hfinite
  have hτ : τ = .E7 ∨ τ = .E8 := by
    rcases hτRaw with hF4 | hE7 | hE8
    · subst τ
      rcases htag with h7 | h8
      · simp [GGQ2LieRank, h7, Tag.rank] at hτrank
      · simp [GGQ2LieRank, h8, Tag.rank] at hτrank
    · exact Or.inl hE7
    · exact Or.inr hE8
  rw [hcard]
  exact four_dvd_aut_of_quasisimple_component S
    (by rcases hτ with rfl | rfl <;> simp) hq hAlg hρ hT ha3 h1 i hQ

theorem four_dvd_image_of_F4 {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .F4)
    (hmark : GGInnerDiagOnLabel (fun _ lab2 => lab2 = lab) 3 Bs L)
    (hidx : ((Subgroup.centralizer (L : Set G)).subgroupOf Bs).index = 3 ^ GGQ2LieRank lab)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) :
    4 ∣ Nat.card (ggAutomizer ((J.subgroupOf L).map (MulAut.conj : L →* MulAut L))
      (ggGamma L hN).range) := by
  obtain ⟨τ, K, hfield, hfinite, S, a, i, hτRaw, hτrank, hq, hAlg, hρ,
    hT, ha3, h1, hQ, hcard⟩ :=
    exists_rationalComponent_of_full_marking hS hq2 (Or.inl htag) hmark hidx hN
  letI := hfield
  letI := hfinite
  have hτ : τ = .F4 := by
    rcases hτRaw with hF4 | hE7 | hE8
    · exact hF4
    · subst τ
      simp [GGQ2LieRank, htag, Tag.rank] at hτrank
    · subst τ
      simp [GGQ2LieRank, htag, Tag.rank] at hτrank
  subst τ
  haveI : CharP (AlgebraicClosure K) 2 :=
    LangRat.charP_two_of_langSetup_q_eq_two_pow S (f := 1) (by simpa using hq)
  rw [hcard]
  exact four_dvd_aut_of_quasisimple_F4 S hq hAlg hρ hT ha3 h1 i hQ

end CFSG.StandardType.QTwoCav

end
