module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNonclassicalSpecs
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeReturnedFrame
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeNCGroup
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRG
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit
public import CFSG.LocalAnalysis.StandardType.GGLangExhaust

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.LieType.Chevalley
  CFSG.StandardType.S2MathFi1035Pos CFSG.LieType.AlgebraicGroups
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.LieCore CFSG.RankThree.PartOne.KE
open CFSG.Open (StatedLieTag)

theorem rckNC_rootPosNbr_of_via
    {X : Type} [Group X] (K R : Subgroup X) (M : LieUniversal) (g : ℕ)
    (hM : StandardReturnAt M g) (β : Fin M.D.rank → ℤ) (hβ : β ∈ M.D.roots)
    (hlong : GGLongRoot M.D β) (hvia : GGRootVia M K R β) : GGRootPosNbr K R := by
  rcases hM with ⟨t, n, hpos, hadm, rfl⟩ | ⟨F, hF, hFin, σ, hT, rfl⟩
  · exact Or.inl ⟨t, n, g, β, hpos, hadm.2.1, hβ, Or.inl hlong, hvia⟩
  · exact Or.inr ⟨F, hF, hFin, σ, g, β, hT, hlong, hvia⟩

theorem rckNC_etaK {X Y : Type} [Group X] [Group Y] (G₀ K : Subgroup X) (hKG : K ≤ G₀)
    (η : ↥G₀ →* Y) (Kb : Subgroup Y) (hK : (K.subgroupOf G₀).map η = Kb)
    (hker : η.ker = Subgroup.center ↥G₀) :
    ∃ ηK : ↥K →* ↥Kb, Function.Surjective ηK ∧
      (∀ x : ↥K, (ηK x : Y) = η ⟨(x : X), hKG x.2⟩) ∧ ηK.ker ≤ Subgroup.center ↥K := by
  have hmem : ∀ x : ↥K, η ⟨(x : X), hKG x.2⟩ ∈ Kb := fun x => by
    rw [← hK]; exact ⟨⟨(x : X), hKG x.2⟩, (Subgroup.mem_subgroupOf).2 x.2, rfl⟩
  refine ⟨(η.comp (Subgroup.inclusion hKG)).codRestrict Kb hmem, ?_, fun x => rfl, ?_⟩
  · intro q
    have hq : (q : Y) ∈ (K.subgroupOf G₀).map η := by rw [hK]; exact q.2
    obtain ⟨k, hk, hkq⟩ := hq
    exact ⟨⟨(k : X), (Subgroup.mem_subgroupOf).1 hk⟩, Subtype.ext hkq⟩
  · intro x hx
    have h1 : η ⟨(x : X), hKG x.2⟩ = 1 := by
      have h2 : (((η.comp (Subgroup.inclusion hKG)).codRestrict Kb hmem x : ↥Kb) : Y) = 1 := by
        rw [MonoidHom.mem_ker.mp hx]; rfl
      exact h2
    have hc : (⟨(x : X), hKG x.2⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := by
      rw [← hker]; exact h1
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have := Subgroup.mem_center_iff.mp hc ⟨(y : X), hKG y.2⟩
    simpa using congrArg Subtype.val this

theorem rckNC_pow_coord {τ : Tag} {a : Fin τ.rank → GGLˣ} {p : ℕ} (hap : ∀ j, a j ^ p = 1) :
    rootDiagUnit τ a ^ p = 1 := by
  have h1 : a ^ p = 1 := funext fun j => by simpa using hap j
  calc rootDiagUnit τ a ^ p = rootDiagUnitHom τ GGL (a ^ p) := by
        rw [map_pow]
        rfl
    _ = 1 := by rw [h1, map_one]

theorem rckNC_adeTag {t : StatedLieTag}
    (h : t = .PSL ∨ t = .PSU ∨ t = .POmegaPlus ∨ t = .POmegaMinus ∨ t = .E6 ∨ t = .E7 ∨
      t = .E8 ∨ t = .twistedE6) : GGPosTag t ∧ t ≠ .PSp ∧ t ≠ .F4 := by
  rcases h with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [GGPosTag]

theorem rckNC_adeModel_standard
    {M : LieUniversal} {g : ℕ} (h : RCKADEModel M g) : StandardReturnAt M g := by
  rcases h with ⟨t, n, htag, hadm, hM⟩ | h
  · exact Or.inl ⟨t, n, (rckNC_adeTag htag).1, hadm, hM⟩
  · exact Or.inr h

theorem rckNC_comp_eq_of_centralizes {X : Type} [Group X] (K J : Subgroup X) (d : X)
    (hKqs : CFSG.Assembly.IsQuasisimple ↥K)
    (hcomp : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    (hcent : ∀ x ∈ K, d * x * d⁻¹ = x) : J = K := by
  have hKd : K ⊓ Subgroup.centralizer {d} = K := by
    apply inf_eq_left.mpr
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    have h1 := hcent x hx
    calc d * x = d * x * d⁻¹ * d := by group
      _ = x * d := by rw [h1]
  rw [hKd] at hcomp
  obtain ⟨hJK, hsn, hJqs⟩ := hcomp
  have hsn' : (J.subgroupOf K).IsSubnormal :=
    (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJK).mp hsn
  have hKq' : CFSG.IsQuasisimple ↥K :=
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff ↥K).2.1).mpr hKqs
  rcases CFSG.CGT.PushingUpLit.CGT6.isSubnormal_le_center_or_eq_top_of_quasisimple hKq' hsn' with
    hle | htop
  · exfalso
    have hcomm : ∀ x y : ↥J, y * x = x * y := fun x y => by
      have hx : (⟨(x : X), hJK x.2⟩ : ↥K) ∈ Subgroup.center ↥K :=
        hle (show (⟨(x : X), hJK x.2⟩ : ↥K) ∈ J.subgroupOf K from x.2)
      have h2 := Subgroup.mem_center_iff.mp hx ⟨(y : X), hJK y.2⟩
      exact Subtype.ext (by simpa using congrArg Subtype.val h2)
    have hctop : Subgroup.center ↥J = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      exact hcomm x y
    haveI : IsSimpleGroup (↥J ⧸ Subgroup.center ↥J) := hJqs.2
    obtain ⟨q, hq⟩ := exists_ne (1 : ↥J ⧸ Subgroup.center ↥J)
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    apply hq
    rw [QuotientGroup.eq_one_iff, hctop]
    exact Subgroup.mem_top _
  · refine le_antisymm hJK fun x hx => ?_
    have h1 : (⟨x, hx⟩ : ↥K) ∈ J.subgroupOf K := by rw [htop]; exact Subgroup.mem_top _
    exact h1

theorem rckNC_irg_ade
    (hIRG : RCKIntrinsicRoot) {X : Type} [Group X] [Finite X] (J R Rm : Subgroup X)
    (hqs : CFSG.Assembly.IsQuasisimple ↥J) (hodd : Odd (Nat.card (Subgroup.center ↥J)))
    (hpos : GGRootPosJ J R Rm) (MJ : LieUniversal) (g : ℕ) (hMJ : RCKADEModel MJ g)
    (φ : MJ.K →* X) (hφr : φ.range = J) (hφk : φ.ker ≤ Subgroup.center MJ.K) :
    ∃ (β : Fin MJ.D.rank → ℤ) (u : MJ.K), β ∈ MJ.D.roots ∧ GGLongRoot MJ.D β ∧
      R = ggRootSub MJ.D φ β u := by
  obtain ⟨h1, h2⟩ := hIRG X J R Rm hqs hodd hpos
  rcases hMJ with ⟨t', n', htag, hadm, rfl⟩ | ⟨F, hF, hFin, σ, hT, rfl⟩
  · obtain ⟨hpt, hnp, hnf⟩ := rckNC_adeTag htag
    obtain ⟨β, u, hβ, hl, hR, -⟩ := h1 t' n' g φ ⟨hpt, hadm⟩ hφr hφk
    refine ⟨β, u, hβ, ?_, hR⟩
    rcases hl with hl | ⟨hsp, -⟩
    · exact hl
    · exfalso
      rcases hsp with ⟨h, -⟩ | h
      · exact hnp h
      · exact hnf h
  · obtain ⟨β, u, hβ, hl, hR, -⟩ := h2 F σ g φ hT hφr hφk
    exact ⟨β, u, hβ, hl, hR⟩

theorem rckNC_map_conj_conj {Y : Type*} [Group Y] (P : Subgroup Y) (k y : Y) :
    (P.map (MulAut.conj k).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      P.map (MulAut.conj (y * k)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem rckNC_orbit_one {τ τK : Tag} {ρ : Equiv.Perm (Fin τ.rank → ℤ)}
    {ρK : Equiv.Perm (Fin τK.rank → ℤ)} {Ψ ΨJ : Set (Fin τ.rank → ℤ)}
    {ι : (Fin τ.rank → ℤ) → (Fin τK.rank → ℤ)} {m : ℕ}
    (hm : 0 < m) (hJΨ : ΨJ ⊆ Ψ) (hJm : componentOrbitLength ρ ΨJ = m)
    (hequiv : ∀ γ ∈ Ψ, ι ((ρ : (Fin τ.rank → ℤ) → _)^[m] γ) =
      (ρK : (Fin τK.rank → ℤ) → _) (ι γ)) :
    componentOrbitLength ρK (ι '' ΨJ) = 1 := by
  have hne : {s : ℕ | 0 < s ∧ (ρ : (Fin τ.rank → ℤ) → _)^[s] '' ΨJ = ΨJ}.Nonempty := by
    by_contra hemp
    rw [Set.not_nonempty_iff_eq_empty] at hemp
    unfold componentOrbitLength at hJm
    rw [hemp, Nat.sInf_empty] at hJm
    omega
  have hJstab : (ρ : (Fin τ.rank → ℤ) → _)^[m] '' ΨJ = ΨJ := by
    have h := (Nat.sInf_mem hne).2
    unfold componentOrbitLength at hJm
    rwa [hJm] at h
  have h1 : 1 ∈ {s : ℕ | 0 < s ∧
      (ρK : (Fin τK.rank → ℤ) → _)^[s] '' (ι '' ΨJ) = ι '' ΨJ} := by
    refine ⟨Nat.one_pos, ?_⟩
    rw [Function.iterate_one, ← Set.image_comp]
    calc ((ρK : (Fin τK.rank → ℤ) → _) ∘ ι) '' ΨJ
        = (ι ∘ (ρ : (Fin τ.rank → ℤ) → _)^[m]) '' ΨJ :=
          Set.image_congr fun γ hγ => (hequiv γ (hJΨ hγ)).symm
      _ = ι '' ((ρ : (Fin τ.rank → ℤ) → _)^[m] '' ΨJ) := Set.image_comp ι _ _
      _ = ι '' ΨJ := by rw [hJstab]
  unfold componentOrbitLength
  exact le_antisymm (Nat.sInf_le h1) (Nat.sInf_mem ⟨1, h1⟩).1

theorem rckNonclassicalArm_of_pieces
    (hRet : RCKCarrierRet) (hPair : RCKCarrierPairADE) (hInc : RCKFrameIncidence)
    (hEnv : RCKStdEnvelope) (hCI : RCKCompImage) (hOne : RCKRelOneUse)
    (hTr : RCKClassTransport) (hTwo : RCKRootGroupTwo) (hIRG : RCKIntrinsicRoot) :
    RCKNonclassicalArm := by
  intro hRel X _ _ t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp hshape
  have hfp0 := hfp
  obtain ⟨hbr, htoral, hKG, hker, hrange, hq, hΦ, hη, hE', hEt, hEel, hfwd, hrE, hr1, hap, hpe,
    hK, hqs, hKqs, hoddK, hB1N, d, hdD, hdne, hJcomp⟩ := hfp0
  have hcfg' := hcfg
  unfold RCKRPConfig at hcfg'
  obtain ⟨-, -, hp, hp2, -, hB1A, hDB1, -, -, -, -, -, -, -, -, -, -, -, -, hoddJ, -, -, -, -,
    -, -, -, hpos, -, -, -, hJK, -⟩ := hcfg'
  haveI hKperf : Group.IsPerfect ↥K := ⟨hKqs.1⟩
  haveI hJperf : Group.IsPerfect ↥J := ⟨hJcomp.2.2.1⟩
  have hrT : rootDiagUnit (langTag t) a ∈ S.D.torus := hEt hrE
  have hapow : rootDiagUnit (langTag t) a ^ p = 1 := rckNC_pow_coord hap
  obtain ⟨M, φ, τK, SK, κ, ι, hMod, hstd, hsurj, hφker, hMfin, hMperf, hMsplit,
    ⟨βK, hβK, hlongK, γ₀, hγ₀, z₀, hz₀, hst₀p, hst₀m, hposK, -⟩, -, hτK, hqK, hκker, hκrange,
    hbij, -, hiform, hequiv, htorus⟩ := hRet (langTag t) S a hrT p hp hp2 hapow i f hq hqs hshape
  haveI := hMfin
  obtain ⟨ηK, hηKs, hηKv, hηKk⟩ := rckNC_etaK G₀ K hKG η _ hK hker
  set cK : ↥K →* ModGL τK GGL := κ.comp ηK with hcKdef
  have hcKker : cK.ker ≤ Subgroup.center ↥K := rck_ker_comp_le_center ηK κ hηKk hκker.le
  have hcKrange : cK.range = SK.Γ := by
    rw [hcKdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hηKs, Subgroup.map_top]
    exact hκrange
  have hdA : d ∈ A := hB1A (hDB1 hdD)
  obtain ⟨bt, hbtE, hbtP⟩ := hfwd d hdA
  have hbtT : bt ∈ S.D.torus := hEt hbtE
  obtain ⟨tt, htt, hcompat, hrootval⟩ := htorus bt hbtT
  have hdN : d ∈ Subgroup.normalizer (K : Set X) := hB1N (hDB1 hdD)
  have hcK : ∀ (x : ↥K) (hx : d * (x : X) * d⁻¹ ∈ K),
      cK ⟨d * (x : X) * d⁻¹, hx⟩ = tt * cK x * tt⁻¹ := by
    intro x hx
    have h1 := hbtP ⟨(x : X), hKG x.2⟩ (hKG hx)
    have hηd : (ηK ⟨d * (x : X) * d⁻¹, hx⟩ : ModGL (langTag t) GGL) =
        bt * (ηK x : ModGL (langTag t) GGL) * bt⁻¹ := by
      rw [hηKv, hηKv]
      exact h1
    have hmemb : bt * (ηK x : ModGL (langTag t) GGL) * bt⁻¹ ∈
        rationalComponent S.ρ S.Γ (rootCharHom a) i := by
      rw [← hηd]
      exact (ηK ⟨d * (x : X) * d⁻¹, hx⟩).2
    have heq : ηK ⟨d * (x : X) * d⁻¹, hx⟩ =
        ⟨bt * (ηK x : ModGL (langTag t) GGL) * bt⁻¹, hmemb⟩ := Subtype.ext hηd
    show κ (ηK ⟨d * (x : X) * d⁻¹, hx⟩) = tt * κ (ηK x) * tt⁻¹
    rw [heq]
    exact hcompat (ηK x) hmemb
  have hTT : tt ∈ torusGroup τK GGL := (mem_twistedTorusOf.1 htt).1
  have hbtT' : bt ∈ torusGroup (langTag t) GGL := (mem_twistedTorusOf.1 hbtT).1
  have hbtp : bt ^ p = 1 := hEel.2 bt hbtE
  have hbc : ∀ j, rckTorusCoord bt j ^ p = 1 := rck_coord_pow hbtT' hbtp
  have haK : rootDiagUnit τK (rckTorusCoord tt) = tt := rck_rootDiagUnit_coord hTT
  have haKp : ∀ j : Fin τK.rank, rckTorusCoord tt j ^ p = 1 := by
    intro j
    obtain ⟨γ, hγΨ, hγ⟩ := hbij.surjOn (isRoot_single τK j)
    have h1 : rckRootVal tt (ι γ) = rckRootVal bt γ := hrootval γ hγΨ
    have h2 : rckRootVal tt (Pi.single j 1) = rckTorusCoord tt j := by
      have h3 := rootChar_nsmul_single (rckTorusCoord tt) j 1
      rw [one_smul, pow_one] at h3
      exact h3
    rw [← h2, ← hγ, h1]
    exact CFSG.RankThree.PartOne.KE.CTTorus.rootChar_pow_eq_one hbc γ
  have haKT : rootDiagUnit τK (rckTorusCoord tt) ∈ SK.D.torus := by rw [haK]; exact htt
  have haKpow : rootDiagUnit τK (rckTorusCoord tt) ^ p = 1 := rckNC_pow_coord haKp
  have haKne : rootDiagUnit τK (rckTorusCoord tt) ≠ 1 := by
    intro h1
    rw [haK] at h1
    have hcent : ∀ x : ↥K, d * (x : X) * d⁻¹ = (x : X) := by
      intro x
      refine rck_conj_commutes_of_central K d hdN (fun y hy => ?_) x
      apply hcKker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcK y hy, h1]
      simp
    exact hKJ (rckNC_comp_eq_of_centralizes K J d hKqs hJcomp (fun x hx => hcent ⟨x, hx⟩)).symm
  have hτK' : τK ≠ Tag.G2 := by rcases hτK with rfl | rfl | rfl <;> decide
  have hpGGL : (p : GGL) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ p := (CharP.cast_eq_zero_iff GGL 2 p).mp h0
    rcases (Nat.Prime.eq_one_or_self_of_dvd hp 2 h2) with h | h
    · omega
    · exact hp2 h.symm
  have hJcI := hCI K J d cK tt hcKker hdN hcK hJcomp
  have hJcI' : IsComponentOf ((J.subgroupOf K).map cK)
      (SK.Γ ⊓ Subgroup.centralizer {rootDiagUnit τK (rckTorusCoord tt)}) := by
    rw [haK, ← hcKrange]
    exact hJcI
  obtain ⟨j, hjqs, hjeq⟩ :=
    CFSG.StandardType.LangRat.exists_rationalComponent_eq_of_isComponentOf_of_ne_G2 SK hτK' hp
      hpGGL haKT haKp haKne (CFSG.Assembly.isComponentOf_iff_open.mp hJcI')
  have hjshape : RCKADEShape SK.ρ (rootCharHom (rckTorusCoord tt)) j :=
    hEnv τK (by rcases hτK with h | h | h <;> simp [h]) SK p hp hp2 (rckTorusCoord tt) haKT haKne
      haKp j hjqs
  have hrc : ∀ γ ∈ componentRoots (rootCharHom a) i,
      rootCharHom (rckTorusCoord tt) (Multiplicative.ofAdd (ι γ)) =
        rootCharHom (rckTorusCoord bt) (Multiplicative.ofAdd γ) := fun γ hγ => hrootval γ hγ
  obtain ⟨iJ, hiJ⟩ := hTr a (rckTorusCoord bt) (rckTorusCoord tt) i ι hbij hiform hrc j
  have hbcE : rootDiagUnit (langTag t) (rckTorusCoord bt) ∈ E' := by
    rw [rck_rootDiagUnit_coord hbtT']
    exact hbtE
  have hiJΨ : componentRoots ((rootCharHom a).prod (rootCharHom (rckTorusCoord bt))) iJ ⊆
      componentRoots (rootCharHom a) i := by
    rw [hiJ]
    intro γ hγ
    exact hγ.1
  have hs := hOne hRel X t n f ψ p G₀ A B₁ D J L R Rm K e ht hcfg hKJ θ A' η E' S a i hfp
    (rckTorusCoord bt) hbcE hbc iJ hiJΨ hshape.excShape
  obtain ⟨hs0, -, -⟩ := outer_componentOrbitLength_spec S hrT i
  have hRj : componentRoots (rootCharHom (rckTorusCoord tt)) j =
      ι '' componentRoots ((rootCharHom a).prod (rootCharHom (rckTorusCoord bt))) iJ := by
    rw [hiJ]
    ext γ'
    constructor
    · intro hγ'
      obtain ⟨hk, hkj⟩ := hγ'
      obtain ⟨γ, hγΨ, hγ⟩ := hbij.surjOn hk.1
      refine ⟨γ, ⟨hγΨ, ?_⟩, hγ⟩
      rw [hγ]
      exact ⟨hk, hkj⟩
    · rintro ⟨γ, ⟨hγΨ, hγj⟩, rfl⟩
      exact hγj
  have horb1 :
      componentOrbitLength SK.ρ (componentRoots (rootCharHom (rckTorusCoord tt)) j) = 1 := by
    rw [hRj]
    exact rckNC_orbit_one hs0 hiJΨ hs hequiv
  obtain ⟨MJ, φJ, hModJ, hADE0, hφJr, hφJk, hMJfin, hMJperf, hMJsplit, hpairJ⟩ :=
    hPair τK 5 SK (rckTorusCoord tt) haKT p hp hp2 haKpow j
      (f * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) hqK hjshape hjqs
  have hADE : RCKADEModel MJ (f * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) := by
    have h1 := hADE0
    rw [horb1, mul_one] at h1
    exact h1
  haveI := hMJfin
  have hrangeJ : φJ.range = (J.subgroupOf K).map cK := by rw [hφJr]; exact hjeq.symm
  obtain ⟨αJ, hαJs, hαJ⟩ := rck_exists_lift K J hJK cK hcKker hoddK MJ.K hMJsplit φJ hrangeJ
  have hφJX_range : (J.subtype.comp αJ).range = J := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hαJs, Subgroup.map_top,
      Subgroup.range_subtype]
  have hφJX_ker : (J.subtype.comp αJ).ker ≤ Subgroup.center MJ.K := by
    intro x hx
    apply hφJk
    have h1 : ((αJ x : ↥J) : X) = 1 := MonoidHom.mem_ker.mp hx
    have h2 : (⟨((αJ x : ↥J) : X), hJK (αJ x).2⟩ : ↥K) = 1 := Subtype.ext h1
    rw [MonoidHom.mem_ker, ← hαJ x, h2, map_one]
  obtain ⟨β, u, hβ, hlongβ, hRβ⟩ := rckNC_irg_ade hIRG J R Rm hJcomp.2.2 hoddJ hpos MJ _ hADE
    (J.subtype.comp αJ) hφJX_range hφJX_ker
  obtain ⟨γ, hγΨ, z, hz, hstab1, hstab2, hpU, -⟩ := hpairJ horb1 β hβ hlongβ
  obtain ⟨k, hkΓ, hkU, -⟩ := hInc τK hτK SK γ γ₀ hγΨ.1.1 hγ₀ z
    (torus_sup_rootSpan_le_adjointGroup _ hz) z₀ hz₀ hstab1 hstab2 hst₀p hst₀m
  have hrangeK' : (κ.comp φ).range = SK.Γ := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hsurj, Subgroup.map_top]
    exact hκrange
  have hrangeK : (κ.comp φ).range = (K.subgroupOf K).map cK := by
    rw [hrangeK', Subgroup.subgroupOf_self, Subgroup.map_top, hcKrange]
  obtain ⟨αK, hαKs, hαK⟩ := rck_exists_lift K K le_rfl cK hcKker hoddK M.K hMsplit (κ.comp φ)
    hrangeK
  have hy : φJ u * k ∈ (κ.comp φ).range := by
    have h1 : φJ u ∈ φJ.range := ⟨u, rfl⟩
    rw [hrangeJ] at h1
    rw [hrangeK', ← hcKrange]
    refine mul_mem (Subgroup.map_le_range cK _ h1) ?_
    rw [← hcKrange] at hkΓ
    exact hkΓ
  obtain ⟨uK, huK⟩ := hy
  let ψJ : MJ.K →* ↥K := (Subgroup.inclusion hJK).comp αJ
  have hψJ : cK.comp ψJ = φJ := MonoidHom.ext fun s => hαJ s
  have hαK' : cK.comp αK = κ.comp φ := MonoidHom.ext fun s => hαK s
  set TJ : Subgroup ↥K := ((MJ.D.rootGroup β).map (MulAut.conj u).toMonoidHom).map ψJ with hTJ
  set TK : Subgroup ↥K := ((M.D.rootGroup βK).map (MulAut.conj uK).toMonoidHom).map αK with hTK
  have hTJc : TJ.map cK = ((rootSubgroup τK GGL γ₀).map (MulAut.conj z₀).toMonoidHom ⊓
      SK.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj (φJ u * k)).toMonoidHom := by
    rw [hTJ, Subgroup.map_map, hψJ, rck_map_conj_map, hpU, hkU, rckNC_map_conj_conj]
  have hTKc : TK.map cK = ((rootSubgroup τK GGL γ₀).map (MulAut.conj z₀).toMonoidHom ⊓
      SK.D.step.eqLocus (MonoidHom.id _)).map (MulAut.conj (φJ u * k)).toMonoidHom := by
    rw [hTK, Subgroup.map_map, hαK', rck_map_conj_map, hposK, huK]
  have hstdJ : StandardReturnAt MJ
      (f * componentOrbitLength S.ρ (componentRoots (rootCharHom a) i)) :=
    rckNC_adeModel_standard hADE
  have hTwoJ : IsPGroup 2 TJ :=
    ((hTwo MJ _ hstdJ β hβ).map (MulAut.conj u).toMonoidHom).map ψJ
  have hTwoK : IsPGroup 2 TK :=
    ((hTwo M _ hstd βK hβK).map (MulAut.conj uK).toMonoidHom).map αK
  have hodd' : Odd (Nat.card cK.ker) := hoddK.of_dvd_nat (Subgroup.card_dvd_of_le hcKker)
  have hTeq : TJ = TK :=
    rck_rootUnique cK hcKker hodd' TJ TK hTwoJ hTwoK (hTJc.trans hTKc.symm)
  have hRT : R = TJ.map K.subtype := by
    rw [hRβ, hTJ, Subgroup.map_map]
    rfl
  have hvia : GGRootVia M K R βK := by
    refine ⟨K.subtype.comp αK, ?_, ?_, uK, ?_⟩
    · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hαKs, Subgroup.map_top,
        Subgroup.range_subtype]
    · intro x hx
      have h1 : αK x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
      have h2 : x ∈ (κ.comp φ).ker := by
        rw [MonoidHom.mem_ker, ← hαK']
        show cK (αK x) = 1
        rw [h1, map_one]
      exact rck_ker_comp_le_center φ κ hφker hκker.le h2
    · rw [hRT, hTeq, hTK, Subgroup.map_map]
      rfl
  exact rckNC_rootPosNbr_of_via K R M _ hstd βK hβK hlongK hvia

theorem rckExcReturnModelAt_of_pieces
    (hSL : RCKCarrierSL) (hA1 : RCKCarrierA1) (hSU : RCKCarrierSU) (hSpF4 : RCKCarrierSpF4)
    (hSpB2 : RCKCarrierSpB2) (hSpin : RCKCarrierSpinPlus) (hTwoD : RCKCarrierTwoD)
    (hTrf : RCKPinnedOfFrameCover) (hNo : RCKNoSmall) (hEnvC : RCKClassEnvelope)
    (hRet : RCKCarrierRet) (hPair : RCKCarrierPairADE) (hInc : RCKFrameIncidence)
    (hEnv : RCKStdEnvelope) (hCI : RCKCompImage) (hOne : RCKRelOneUse)
    (hTr : RCKClassTransport) (hTwo : RCKRootGroupTwo) (hIRG : RCKIntrinsicRoot) :
    RCKExcReturnModelAt :=
  rckExcReturnModelAt_of_contracts hSL hA1 hSU hSpF4 hSpB2 hSpin hTwoD hTrf hNo hEnvC
    (rckNonclassicalArm_of_pieces hRet hPair hInc hEnv hCI hOne hTr hTwo hIRG)

end CFSG.StandardType.RCKRP
