module

public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HFrameR
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HTwo
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HLang
public import CFSG.RankThree.PartTwo.Sec12.Hering129D4HStd
public import CFSG.RankThree.PartTwo.Sec21.Item219LieProofD4U2

public section

set_option linter.unusedSectionVars false

namespace CFSG.RankThree.PartTwo.Sec12

namespace Hering129D4H

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.Blueprint CFSG.Blueprint.Chevalley
  CFSG.LieType.Chevalley CFSG.RankThree.Chevalley CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
  CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.RankThree.PartTwo.Sec19 CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KGD
  CFSG.RankThree.Lattice CFSG.RankThree.PartTwo.Sec11 CFSG.RankThree.PartTwo.Sec12.Hering129L
  CFSG.RankThree.PartTwo.Sec21.Item219LieProof CFSG.RankThree.PartTwo.Sec4.E27


section Final

variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X} (P : D4Par n X σ)

theorem exists_conj_zStd {ζ : (AlgebraicClosure X)ˣ} (hζ : orderOf ζ = 3)
    {g : ModGL TwistTag.D4.tag (AlgebraicClosure X)}
    (hgG : g ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure X)) {c : C0 σ}
    (hc : threeSixEmb' (AlgebraicClosure X) X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT)) :
    ∃ γ₀ : C0 σ, γ₀ * c * γ₀⁻¹ = zStd P := by
  haveI := P.charP
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure X with hL
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap X L).injective 2
  have hζ3 := pow_three_of_orderOf hζ
  have hσ3 : σ ^ 3 = 1 := P.sigma_pow_three
  obtain ⟨k', hk', hzk⟩ := exists_conj_dA_of_mem_short hσ3 hζ (zStd_mem P) (zStd_pow_three P)
    (zStd_ne_one P)
  have hd : rootDiagUnit TwistTag.D4.tag (tup ζ gT) =
      (canonicalRep (coxeterSystem TwistTag.D4.tag) L
        ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) *
          canonicalRep (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]) := by
    rw [rootDiagUnit_tup_eq_conj hζ3 [3, 2, 1, 0, 2, 3] gT,
      show wordExp [3, 2, 1, 0, 2, 3] gT = gA by decide]
  have hk : g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹ ∈
        adjointGroup TwistTag.D4.tag L :=
    mul_mem hgG (inv_mem (canonicalRep_mem_adjointGroup _ L _))
  have h1 : threeSixEmb X L σ c = g * rootDiagUnit TwistTag.D4.tag (tup ζ gT) * g⁻¹ := by
    have h := threeSixEmb'_apply (g := g) (K := X) (σ := σ) (Ω := L) c
    rw [hc] at h
    rw [h]
    group
  have hxk : triEmb X σ L c = (g * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹) *
        rootDiagUnit TwistTag.D4.tag (tup ζ gA) * (g * (canonicalRep
          (coxeterSystem TwistTag.D4.tag) L
            ((coxeterSystem TwistTag.D4.tag).wordProd [3, 2, 1, 0, 2, 3]))⁻¹)⁻¹ := by
    change threeSixEmb X L σ c = _
    rw [h1, hd]
    group
  obtain ⟨γ, hγ⟩ := exists_conj_of_triEmb_conj (ℓ := 2) (f := n) P.one_le P.card P.frob
    (isPointIrreducible_gA hζ) hk' hk hzk hxk
  exact ⟨γ⁻¹, by rw [← hγ]; group⟩

section RSL

variable {L : Type} [Field L] [Algebra X L] [IsAlgClosure X L] [CharP L 2]
  {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ (2 ^ n)) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
  (hqε : ((2 ^ n : ℕ) : ZMod 3) = (ε : ZMod 3)) {ζ : Lˣ} (hζ : orderOf ζ = 3)
  {g : ModGL TwistTag.D4.tag L} (hgG : g ∈ adjointGroup TwistTag.D4.tag L)
  (hFg : trialityFrob L Fr g = g * threeSixN L ε)

include P hFr hε hqε hζ hgG hFg

theorem cE_mem_threeSixTorus :
    rootDiagUnit TwistTag.D4.tag (tup ζ gT) ∈ threeSixTorus L Fr ε := by
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed X
  have hgT : gT = vecV 1 0 := by decide
  rw [hgT]
  exact mem_threeSixTorus_tup_vec hFr hε hqε (pow_three_of_orderOf hζ) 1 0

theorem threeSixEmb_of_phi {c : C0 σ} {d : ModGL TwistTag.D4.tag L}
    (hc : threeSixEmb' L X σ g c = d) : threeSixEmb X L σ c = g * d * g⁻¹ := by
  have h := threeSixEmb'_apply (g := g) (K := X) (σ := σ) (Ω := L) c
  rw [hc] at h
  rw [h]
  group

theorem isSLThreePiAt_R_ge2 (hn : 2 ≤ n) {c : C0 σ}
    (hc : threeSixEmb' L X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT))
    (hA : IsThreeA c (2 ^ n)) :
    Sec4.IsSLThreePiAt ↥(threeSixSingularR L X σ Fr ε vT g) (2 ^ n) := by
  classical
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed X
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq2 : ε = 1 ∨ 2 < 2 ^ n := Or.inr (lt_of_lt_of_le (by norm_num)
    (Nat.pow_le_pow_right (by norm_num) hn))
  obtain ⟨hcomm, hquasi, -⟩ := threeSix_singular_three (ℓ := 2) Nat.prime_two (by decide)
    P.one_le X P.card σ P.frob L Fr hFr hε hq2 g hgG hFg (tup ζ gT)
    (cE_mem_threeSixTorus P hFr hε hqε hζ hgG hFg) (orderOf_rootDiagUnit_tup_gT hζ) vT
    (survivingRoots_tup_gT hζ) c (threeSixEmb_of_phi P hFr hε hqε hζ hgG hFg hc)
  have hRle : threeSixSingularR L X σ Fr ε vT g ≤
      (⊤ : Subgroup (C0 σ)) ⊓ Subgroup.centralizer ({c} : Set (C0 σ)) :=
    le_inf le_top fun r hr => Subgroup.mem_centralizer_singleton_iff.2
      (R_comm_c P hFr hζ hgG hFg hc r hr)
  have hres : resCent (⊤ : Subgroup (C0 σ)) c = threeSixSingularR L X σ Fr ε vT g := by
    apply le_antisymm
    · rw [← hcomm]
      show inSubgroup perfectResidual ((⊤ : Subgroup (C0 σ)) ⊓
        Subgroup.centralizer ({c} : Set (C0 σ))) ≤ _
      rw [top_inf_eq]
      exact inSubgroup_perfectResidual_le_commutator' _
    · haveI := hquasi.1
      exact le_inSubgroup_perfectResidual_of_isPerfect hRle hquasi.1
  exact isSLThreePiAt_congr (MulEquiv.subgroupCongr hres) hA.2.2

theorem isSLThreePiAt_R_one (hn1 : n = 1) (hε1 : ε = -1) {c : C0 σ}
    (hc : threeSixEmb' L X σ g c = rootDiagUnit TwistTag.D4.tag (tup ζ gT)) :
    Sec4.IsSLThreePiAt ↥(threeSixSingularR L X σ Fr ε vT g) (2 ^ n) := by
  classical
  subst hn1
  subst hε1
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed X
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, U, hU, ⟨e⟩⟩ := threeSix_unitary_model_two (ℓ := 2) (f := 1) Nat.prime_two
    (by decide) le_rfl X P.card σ P.frob L Fr hFr g hgG hFg (tup ζ gT)
    (cE_mem_threeSixTorus P hFr hε hqε hζ hgG hFg) (orderOf_rootDiagUnit_tup_gT hζ) vT
    (survivingRoots_tup_gT hζ) c (threeSixEmb_of_phi P hFr hε hqε hζ hgG hFg hc)
  set R := threeSixSingularR L X σ Fr (-1) vT g with hR
  let s : ↥R →* GL (Fin 3) L := U.subtype.comp e.toMonoidHom
  have hs : Function.Injective s := U.subtype_injective.comp e.injective
  have hrange : ∀ Y : GL (Fin 3) L, Y ∈ s.range ↔
      Y ∈ CFSG.RankThree.Classical2.unitarySet (2 ^ 1) 3 := by
    intro Y
    rw [← hU]
    constructor
    · rintro ⟨d, rfl⟩
      exact (e d).2
    · intro hY
      refine ⟨e.symm ⟨Y, hY⟩, ?_⟩
      show ((e (e.symm ⟨Y, hY⟩) : ↥U) : GL (Fin 3) L) = Y
      rw [MulEquiv.apply_symm_apply]
  have hact : ∀ g' ∈ R, ∃ N : GL (Fin 3) L, ∀ d d' : ↥R, (d' : C0 σ) = g' * d * g'⁻¹ →
      s d' = N * s d * N⁻¹ := by
    intro g' hg'
    refine ⟨s ⟨g', hg'⟩, fun d d' h => ?_⟩
    have : d' = ⟨g', hg'⟩ * d * ⟨g', hg'⟩⁻¹ := Subtype.ext h
    rw [this, map_mul, map_mul, map_inv]
  obtain ⟨F, hF, hFd, e', -⟩ := unitary_layer_model_of_interface
    (ℓ := 2) (f := 1) (Ω := L) R R
    (fun g hg d hd => R.mul_mem (R.mul_mem hg hd) (R.inv_mem hg)) le_rfl (by decide)
    (by norm_num) s hs hrange hact
  refine ⟨F, hF, hFd.finite, Or.inr ⟨?_, by norm_num, ⟨e'.trans (MulEquiv.subgroupCongr rfl)⟩⟩⟩
  rw [hFd.card]
  norm_num

end RSL

section Main

theorem conj_mem_commutator_centralizer {G : Type} [Group G] [Finite G] {c z t γ₀ : G}
    (hγ₀ : γ₀ * c * γ₀⁻¹ = z) (ht : t ∈ ⁅Subgroup.centralizer ({z} : Set G),
      Subgroup.centralizer ({z} : Set G)⁆) :
    γ₀⁻¹ * t * γ₀ ∈ ⁅Subgroup.centralizer ({c} : Set G), Subgroup.centralizer ({c} : Set G)⁆ := by
  have hc : γ₀⁻¹ * z * γ₀⁻¹⁻¹ = c := by rw [← hγ₀]; group
  have hcent : Subgroup.centralizer ({c} : Set G) =
      (Subgroup.centralizer ({z} : Set G)).map (MulAut.conj γ₀⁻¹).toMonoidHom := by
    rw [← hc]
    exact centralizer_conj_eq_map γ₀⁻¹ z
  rw [hcent, ← Subgroup.map_commutator]
  refine Subgroup.mem_map.2 ⟨t, ht, ?_⟩
  simp [MulAut.conj_apply]

theorem kf_d4_hess : KF_D4_HESS := by
  classical
  intro n X _ _ σ P
  haveI := P.charP
  haveI : Finite (C0 σ) := finite_C0 (σ := σ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L := AlgebraicClosure X with hL
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap X L).injective 2
  have h3 : ¬ 3 ∣ 2 ^ n := fun h => by
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
    omega
  have hq3 : 2 ^ n % 3 = 1 ∨ 2 ^ n % 3 = 2 := by omega
  obtain ⟨ε, hε, hqε⟩ : ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ((2 ^ n : ℕ) : ZMod 3) = (ε : ZMod 3) := by
    rcases hq3 with h | h
    · refine ⟨1, Or.inl rfl, ?_⟩
      rw [← ZMod.natCast_mod, h]
      rfl
    · refine ⟨-1, Or.inr rfl, ?_⟩
      rw [← ZMod.natCast_mod, h]
      rfl
  have h3L : (3 : L) ≠ 0 := by
    intro h
    have h' : ((3 : ℕ) : L) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff L 2] at h'
    omega
  obtain ⟨ζ, hζ⟩ := exists_units_orderOf_three L h3L
  have hζ3 := pow_three_of_orderOf hζ
  set Fr : L →+* L := iterateFrobenius L 2 n with hFrdef
  have hFr : ∀ c, Fr c = c ^ (2 ^ n) := fun c => iterateFrobenius_def 2 n c
  obtain ⟨g, hgG, hFg⟩ := lang_conjugator_D4 (K := X) (ℓ := 2) P.one_le L (threeSixN L ε)
    (threeSixN_mem_adjointGroup hε)
  have hFg' : trialityFrob L Fr g = g * threeSixN L ε := hFg
  obtain ⟨c, y, F, hF, hc, hy⟩ := exists_hessF_frame P hFr hε hqε hζ hgG hFg'
  have hinj : Function.Injective (threeSixEmb' L X σ g) := threeSixEmb'_injective g
  obtain ⟨γ₀, hγ₀⟩ := exists_conj_zStd P hζ hgG hc
  have hc3 : c ^ 3 = 1 ∧ c ≠ 1 := by
    have hord : orderOf c = 3 := by
      rw [← orderOf_injective (threeSixEmb' L X σ g) hinj c, hc]
      exact orderOf_rootDiagUnit_tup_gT hζ
    exact ⟨pow_three_of_orderOf hord, fun h => by rw [h, orderOf_one] at hord; omega⟩
  have hy3 : y ^ 3 = 1 := hinj (by
    rw [map_pow, hy, map_one, pow_three', ← nw_append, ← nw_append, nw_eq_canonicalRep,
      wordProd_wT_cube, canonicalRep_one])
  have hyc : y ∉ Subgroup.zpowers c := by
    obtain ⟨hab, -, hcF, -, -, hnt, -, -⟩ := hF
    intro h
    have hyF : y ∈ F := (Subgroup.zpowers_le.2 hcF) h
    obtain ⟨f, hf, hne⟩ := hnt
    apply hne
    have h1 : y * f = f * y := congrArg Subtype.val (hab.1.is_comm.comm ⟨y, hyF⟩ ⟨f, hf⟩)
    rw [h1]
    group
  have hRSL : Sec4.IsSLThreePiAt ↥(threeSixSingularR L X σ Fr ε vT g) (2 ^ n) := by
    by_cases hn : 2 ≤ n
    · have hzA : IsThreeA (zStd P) (2 ^ n) := d4_isThreeA P hn (zStd_mem P)
        (orderOf_eq_prime (zStd_pow_three P) (zStd_ne_one P))
      have hcA : IsThreeA c (2 ^ n) := by
        have := isThreeA_conj hzA γ₀⁻¹
        rwa [show γ₀⁻¹ * zStd P * γ₀⁻¹⁻¹ = c by rw [← hγ₀]; group] at this
      exact isSLThreePiAt_R_ge2 P hFr hε hqε hζ hgG hFg' hn hc hcA
    · have hn1 : n = 1 := by
        have := P.one_le
        omega
      have hε1 : ε = -1 := by
        subst hn1
        rcases hε with rfl | rfl
        · exact absurd hqε (by decide)
        · rfl
      exact isSLThreePiAt_R_one P hFr hε hqε hζ hgG hFg' hn1 hε1 hc
  have hcR := c_mem_R P hFr hζ hgG hFg' hc
  have hyR := y_mem_R P hFr hζ hgG hFg' hy
  have hRc := R_comm_c P hFr hζ hgG hFg' hc
  have htR : γ₀⁻¹ * tStd P * γ₀ ∈ threeSixSingularR L X σ Fr ε vT g :=
    comm_le_R P hFr hζ hgG hFg' hc (conj_mem_commutator_centralizer hγ₀ (tStd_mem_commutator P))
  obtain ⟨γ, hγc, hγy⟩ := exists_conj_std_of_R P hRSL hcR hRc hc3.1 hc3.2 hyR hy3 hyc hγ₀ htR
  refine ⟨F.map (MulAut.conj γ).toMonoidHom, ?_⟩
  have h := HessF.map (MulAut.conj γ) hF
  have e1 : (MulAut.conj γ) c = zStd P := hγc
  have e2 : (MulAut.conj γ) y = tStd P := hγy
  rw [e1, e2] at h
  exact h

theorem gap129HessD4_holds : Gap129HessD4 := gap129HessD4_of_KF kf_d4_hess

end Main

end Final

end Hering129D4H

end CFSG.RankThree.PartTwo.Sec12
