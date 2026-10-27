module

-- The minimal-counterexample assembly lives here, ABOVE `GorensteinWalter.GW1965`
-- (which public-imports `GorensteinWalter.Defs`, hence the whole Classification
-- machinery): the S3 case analysis needs the [10]-Prop-9 dGroup-quotient supplies
-- (`hasDihedralSylowTwo_of_minimalNormal_dGroupQuotient`,
-- `center_eq_bot_of_minimalNormal_dGroupQuotient`) which live in GW1965, and
-- Classification sits below GW1965 (import direction: GW1965 -> Defs ->
-- Classification). Per the module-layering convention, the theorem moved upward;
-- consumers (Section2/Basic.lean, Section2/Lemma23.lean) import this module.

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.LinearThree
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalNormalKleinFour
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGroupExtension

namespace CFSG
end CFSG
open CFSG

universe u

namespace CFSG.GorensteinWalter

noncomputable section

-- [10, Prop 9, S3] Theorem 1 for a `2`-group: a minimal counterexample that
-- is a `2`-group is a `D`-group (`G/O₂'(G)` is a `2`-group).
private lemma isDGroup_of_isPGroup_of_minimalCounterexample {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) (hG2 : IsPGroup 2 G) : IsDGroup G := by
  have hO : pPrimeCore 2 G = ⊥ := pPrimeCore_two_eq_bot_of_minimalCounterexample hmin
  have hSylowG : HasCyclicOrDihedralSylowTwo G := by
    intro S
    rcases hmin.1 S with ⟨m, hm, e⟩
    right
    exact ⟨m, hm, e⟩
  refine IsDGroup.quotientIsTwoGroup hSylowG ?_
  have e : G ⧸ pPrimeCore 2 G ≃* G := by
    exact (QuotientGroup.quotientMulEquivOfEq (G := G) hO).trans (QuotientGroup.quotientBot (G := G))
  exact IsPGroup.of_equiv hG2 e.symm

/-- [10, Prop 9, S3] The minimal counterexample is simple.
The S3 body: `IsSimpleGroup.mk` with the normal-subgroup clause proved from a
minimal normal `H' ≤ N` (`exists_minimalNormal_of_normal_ne_bot`); `H'` is a
proper subgroup, hence a `D`-group (`properSubgroups_areDGroups`), and the
three `IsDGroup` cases are:
* **Case A (A₇)**: `IsDGroupQuotient H'` from the quotient-isomorphism; the
  supplies `hasDihedralSylowTwo_of_minimalNormal_dGroupQuotient` /
  `center_eq_bot_of_minimalNormal_dGroupQuotient` give the dihedral-Sylow and
  trivial-center hypotheses, `gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7`
  the PSL(2,q)/A₇ classification, and the chain
  `gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow` →
  `gw_prop9_centralizer_of_normal_odd_order_eq_bot` →
  `gw_prop9_dGroup_conclusion_from_minimalNormal` gives `IsDGroup G`,
  contradicting the minimal counterexample (`hmin.2.1`).
* **Case A (linear)**: the same chain, with `IsDGroupQuotient H'` from the
  `PSL₂(K)`/`PGL₂(K)` normal-subgroup clause (the `IsIsoToPSL2OddExists`
  witness via `(inferInstance : Field K)`).
* **Case B (2-group quotient)**: `H'` is a 2-group; the cyclic sub-case uses
  `gw_prop9_cyclic_minimalNormal_normalTwoComplement` and Theorem 1 for a
  normal-2-complement group (`gw_prop9_normalTwoComplement_isDGroup`); the
  non-cyclic sub-case
  derives `H' ≃* DihedralGroup (2^m)` (the Sylow 2 of the 2-group `H'` is
  `H'` itself and non-cyclic), applies the dihedral chain
  (`gw_prop9_centralizer_dihedral_normalTwoComplement`,
  `gw_prop9_centralizer_oddCore_trivial`,
  `gw_prop9_dihedral_normal_subgroup_outer_automorphism`), and the `|H'| = 4`
  Klein-four branch ends in `gw_prop9_subgroup_S4_twoGroup_or_PSL23_or_PGL23`
  (the `2`-group branch contradicts via Theorem 1; the PSL(2,3)/PGL(2,3)
  branches use the universe-lift wrappers in `LinearThree`).  The `|H'| > 4`
  branch is the remaining recorded Case-B glue resist-point. -/
public theorem minimalCounterexample_isSimple
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    IsSimpleGroup G := by
  have hO : pPrimeCore 2 G = ⊥ := pPrimeCore_two_eq_bot_of_minimalCounterexample hmin
  have : Nontrivial G := nontrivial_of_dihedralSylowTwo hmin.1
  refine ⟨?_⟩
  intro H hHnormal
  by_cases hHbot : H = ⊥
  · exact Or.inl hHbot
  · by_cases hHtop : H = ⊤
    · exact Or.inr hHtop
    · exfalso
      rcases exists_minimalNormal_of_normal_ne_bot H hHnormal hHbot hHtop with
        ⟨H', hH'normal, hH'ne, hH'top, hH'min⟩
      have hOH' : pPrimeCore 2 (↥H') = ⊥ :=
        pPrimeCore_two_eq_bot_of_normal_subgroup_of_minimalCounterexample hmin H' hH'normal
      have hDG : IsDGroup H' := properSubgroups_areDGroups hmin H' hH'top
      rcases hDG with ⟨hSylowH, htwoH⟩ | ⟨hSylowH, e7⟩ | ⟨hSylowH, K, hKprime, L, hLnormal, hLindex, hLmodel⟩
      · -- Case B: H' is a 2-group (the paper's pp. 219--220 second paragraph)
        by_cases hH'cyc : IsCyclic H'
        · -- cyclic: |H'| = 2, Lemma 2.2 gives a normal 2-complement of G,
          -- and Theorem 1 holds for G (a normal 2-complement makes
          -- G/O₂'(G) a 2-group)
          have hNPC : Glauberman.NormalPComplement 2 G :=
            gw_prop9_cyclic_minimalNormal_normalTwoComplement hmin H' hH'normal hH'ne hH'min hH'cyc
          -- "and again Theorem 1 holds for 𝔊" (the normal 2-complement bridge)
          have hDG' : IsDGroup G := gw_prop9_normalTwoComplement_isDGroup hmin hNPC
          exact hmin.2.1 hDG'
        · -- non-cyclic: H' is a dihedral 2-group
          have hH'two : IsPGroup 2 (↥H') := by
            have e : (↥H') ⧸ pPrimeCore 2 (↥H') ≃* (↥H') := by
              exact (QuotientGroup.quotientMulEquivOfEq (G := ↥H') hOH').trans (QuotientGroup.quotientBot (G := ↥H'))
            exact IsPGroup.of_equiv htwoH e
          rcases (Sylow.nonempty (p := 2) (G := ↥H')) with ⟨S⟩
          have hcardS : Nat.card (↥((S : Subgroup (↥H')))) = Nat.card (↥H') := by
            rcases (IsPGroup.iff_card.mp hH'two) with ⟨n, hn⟩
            calc
              Nat.card (↥((S : Subgroup (↥H')))) = 2 ^ Nat.factorization (Nat.card (↥H')) 2 :=
                Sylow.card_eq_multiplicity S
              _ = 2 ^ n := by
                congr 1
                have hp2 : Nat.Prime 2 := Nat.prime_two
                rw [hn, Nat.factorization_pow_self hp2]
              _ = Nat.card (↥H') := hn.symm
          have hStop : (S : Subgroup (↥H')) = ⊤ := by
            apply Subgroup.eq_of_le_of_card_ge (H := (S : Subgroup (↥H'))) (K := ⊤)
            · exact le_top
            · simp [hcardS]
          have eS : Nonempty ((S : Subgroup (↥H')) ≃* (↥H')) := by
            rw [hStop]
            exact ⟨Subgroup.topEquiv⟩
          have hSylowS := hSylowH S
          have hH'dihedral : ∃ m : ℕ, 1 ≤ m ∧ Nonempty (H' ≃* DihedralGroup (2 ^ m)) := by
            rcases hSylowS with hScyc | ⟨m, hm, eSd⟩
            · exfalso
              apply hH'cyc
              exact isCyclic_of_surjective (eS.some : ↥S →* ↥H') eS.some.surjective
            · exact ⟨m, hm, ⟨eS.some.symm.trans eSd.some⟩⟩
          have hCNPC : Glauberman.NormalPComplement 2 (↥(Subgroup.centralizer (H' : Set G))) :=
            gw_prop9_centralizer_dihedral_normalTwoComplement hmin H' hH'normal hH'dihedral
          have hCO : oddCoreOf (Subgroup.centralizer (H' : Set G)) = ⊥ :=
            gw_prop9_centralizer_oddCore_trivial hmin H' hH'normal
          have hOuter : ∀ g : G, g ∉ H' →
              ¬ ∃ n : ↥H', ∀ x : ↥H', g * x * g⁻¹ = n * x * n⁻¹ :=
            gw_prop9_dihedral_normal_subgroup_outer_automorphism hmin H' hH'normal hH'dihedral
          by_cases hH'4 : Nat.card (↥H') = 4
          · -- |H'| = 4: H' is a Klein four group
            have : Fintype (↥H') := Fintype.ofFinite _
            have hK4 : IsKleinFour H' := by
              refine ⟨hH'4, ?_⟩
              have hsq : ∀ g : ↥H', g ^ 2 = 1 := by
                intro g
                by_cases hg1 : g = 1
                · rw [hg1]
                  simp
                · have hord : orderOf g ∣ Nat.card (↥H') := by
                    simpa [Nat.card_eq_fintype_card] using (orderOf_dvd_card : orderOf g ∣ Fintype.card (↥H'))
                  have hord_dvd : orderOf g ∣ 4 := by
                    rwa [hH'4] at hord
                  rcases (Nat.dvd_prime_pow Nat.prime_two (m := 2) (i := orderOf g)).mp hord_dvd with ⟨a, ha2, hpow⟩
                  have hnot1 : a ≠ 0 := by
                    intro ha0
                    apply hg1
                    rw [← orderOf_eq_one_iff]
                    simpa [ha0] using hpow
                  have hnot2 : a ≠ 2 := by
                    intro ha2'
                    apply hH'cyc
                    have hgtop : Subgroup.zpowers g = ⊤ := by
                      apply Subgroup.eq_of_le_of_card_ge
                      · exact le_top
                      · have hzg : Nat.card (↥(Subgroup.zpowers g)) = orderOf g := by
                          rw [Nat.card_eq_fintype_card]
                          exact Fintype.card_zpowers (x := g)
                        rw [hzg, hpow, ha2']
                        simp
                        rw [← Nat.card_eq_fintype_card, hH'4]
                    exact (isCyclic_iff_exists_zpowers_eq_top (α := ↥H')).mpr ⟨g, hgtop⟩
                  have ha1 : a = 1 := by omega
                  have hord2 : orderOf g = 2 := by simpa [ha1] using hpow
                  exact (orderOf_dvd_iff_pow_eq_one.mp (by rw [hord2]))
              have hdvd : Monoid.exponent (↥H') ∣ 2 :=
                (Monoid.exponent_dvd_iff_forall_pow_eq_one (n := 2)).mpr hsq
              have hnt : Nontrivial (↥H') := by
                have h1 : 1 < Fintype.card (↥H') := by
                  rw [← Nat.card_eq_fintype_card, hH'4]
                  norm_num
                exact (Fintype.one_lt_card_iff_nontrivial (α := ↥H')).mp h1
              rcases (exists_ne (1 : ↥H')) with ⟨g, hg⟩
              have hgord : orderOf g = 2 := by
                have hsq' := hsq g
                have hdvd2 : orderOf g ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr hsq'
                rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
                · exfalso
                  apply hg
                  exact (orderOf_eq_one_iff.mp h1)
                · exact h2
              have h2dvd : (2 : ℕ) ∣ Monoid.exponent (↥H') := by
                exact hgord.symm ▸ Monoid.order_dvd_exponent g
              exact Nat.dvd_antisymm hdvd h2dvd
            have hemb : ∃ φ : G →* Equiv.Perm (Fin 4), Function.Injective φ :=
              minimalNormal_kleinFour_embeds_S4
                hmin H' hH'normal hH'ne hH'min hK4
            have hS4 := gw_prop9_subgroup_S4_twoGroup_or_PSL23_or_PGL23 hmin.1 hemb
            rcases hS4 with hG2 | hPSL23 | hPGL23
            · have hDG' : IsDGroup G := isDGroup_of_isPGroup_of_minimalCounterexample hmin hG2
              exact hmin.2.1 hDG'
            · -- `G ≅ PSL₂(ZMod 3)` closes through the compiled universe lift.
              exact hmin.2.1 (isDGroup_of_iso_PSL2_three
                (pPrimeCore_two_eq_bot_of_minimalCounterexample hmin) hmin.1 hPSL23)
            · -- `G ≅ PGL₂(ZMod 3)` closes through the same wrapper layer.
              exact hmin.2.1 (isDGroup_of_iso_PGL2_three
                (pPrimeCore_two_eq_bot_of_minimalCounterexample hmin) hmin.1 hPGL23)
          · -- RESIST-GOAL (Case-B glue): `|H'| > 4` — `Aut(H')` is a `2`-group
            -- (`gw_prop9_aut_dihedral_is_twoGroup` transported by `MulAut.congr`),
            -- `C(H')` is a `2`-group (the normal-2-complement + trivial-odd-core
            -- bridge), the embedding `G/C(H') ↪ Aut(H')` needs the injectivity of
            -- the `quotient_center_embed_aut` hom, and `G` is a `2`-group by the
            -- extension argument — then Theorem 1 contradicts `hmin`.
            rcases hH'dihedral with ⟨m, hm, eH⟩
            have hm2 : 2 ≤ m := by
              have hcard : Nat.card (↥H') = 2 * 2 ^ m := by
                calc
                  Nat.card (↥H') = Nat.card (DihedralGroup (2 ^ m)) :=
                    Nat.card_congr eH.some.toEquiv
                  _ = 2 * 2 ^ m := DihedralGroup.nat_card
              by_contra hnot
              have hm1 : m = 1 := by omega
              apply hH'4
              rw [hcard, hm1]
              norm_num
            have hAutModel : IsPGroup 2 (MulAut (DihedralGroup (2 ^ m))) :=
              gw_prop9_aut_dihedral_is_twoGroup hm2
            have hAut : IsPGroup 2 (MulAut (↥H')) :=
              hAutModel.of_equiv (MulAut.congr eH.some).symm
            have hCcore :
                pPrimeCore 2 (↥(Subgroup.centralizer (H' : Set G))) = ⊥ := by
              unfold oddCoreOf at hCO
              exact (Subgroup.map_eq_bot_iff_of_injective
                (pPrimeCore 2 (↥(Subgroup.centralizer (H' : Set G))))
                (Subgroup.centralizer (H' : Set G)).subtype_injective).mp hCO
            have hCtwo : IsPGroup 2 (↥(Subgroup.centralizer (H' : Set G))) :=
              isPGroup_of_normalPComplement_of_pPrimeCore_eq_bot hCNPC hCcore
            rcases quotient_centralizer_mulAut_embedding H' with ⟨φ, hφ⟩
            have hQtwo : IsPGroup 2 (G ⧸ Subgroup.centralizer (H' : Set G)) :=
              hAut.of_injective φ hφ
            have hGtwo : IsPGroup 2 G :=
              isPGroup_of_normal_subgroup_of_quotient
                (Subgroup.centralizer (H' : Set G)) hCtwo hQtwo
            have hDG' : IsDGroup G :=
              isDGroup_of_isPGroup_of_minimalCounterexample hmin hGtwo
            exact hmin.2.1 hDG'
      · -- Case A: H' ≅ A₇
        have hHD : IsDGroupQuotient H' := Or.inl e7
        have hHd : HasDihedralSylowTwo (↥H') :=
          hasDihedralSylowTwo_of_minimalNormal_dGroupQuotient hmin H' hH'normal hH'ne hH'min hHD
        have hZ : Subgroup.center (↥H') = ⊥ :=
          center_eq_bot_of_minimalNormal_dGroupQuotient hmin H' hH'normal hH'ne hH'min hHD
        have hHH : IsIsoToPSL2OddExists H' ∨ Nonempty (H' ≃* alternatingGroup (Fin 7)) :=
          gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7 hmin H' hH'normal hH'ne hH'min hHd hHD
        have hCodd : Nat.Coprime 2 (Nat.card (↥(Subgroup.centralizer (H' : Set G)))) :=
          gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow hmin H' hH'normal hH'min hH'ne hZ hHd
        have hCH : Subgroup.centralizer (H' : Set G) = ⊥ :=
          gw_prop9_centralizer_of_normal_odd_order_eq_bot hmin H' hH'normal hCodd
        have hDG' : IsDGroup G :=
          gw_prop9_dGroup_conclusion_from_minimalNormal hmin H' hH'normal hHH hCH
        exact hmin.2.1 hDG'
      · -- Case A: linear
        have hHD : IsDGroupQuotient H' := by
          rcases hLmodel with hLpsl | hLpgl
          · right
            refine ⟨L, hLnormal, hLindex, Or.inl ?_⟩
            exact ⟨K, (inferInstance : Field K), (inferInstance : Finite K), ⟨hKprime, hLpsl⟩⟩
          · right
            refine ⟨L, hLnormal, hLindex, Or.inr ?_⟩
            exact ⟨K, (inferInstance : Field K), (inferInstance : Finite K), ⟨hKprime, hLpgl⟩⟩
        have hHd : HasDihedralSylowTwo (↥H') :=
          hasDihedralSylowTwo_of_minimalNormal_dGroupQuotient hmin H' hH'normal hH'ne hH'min hHD
        have hZ : Subgroup.center (↥H') = ⊥ :=
          center_eq_bot_of_minimalNormal_dGroupQuotient hmin H' hH'normal hH'ne hH'min hHD
        have hHH : IsIsoToPSL2OddExists H' ∨ Nonempty (H' ≃* alternatingGroup (Fin 7)) :=
          gw_prop9_minimalNormal_dGroup_iso_PSL2_or_A7 hmin H' hH'normal hH'ne hH'min hHd hHD
        have hCodd : Nat.Coprime 2 (Nat.card (↥(Subgroup.centralizer (H' : Set G)))) :=
          gw_prop9_centralizer_odd_of_trivial_center_dihedralSylow hmin H' hH'normal hH'min hH'ne hZ hHd
        have hCH : Subgroup.centralizer (H' : Set G) = ⊥ :=
          gw_prop9_centralizer_of_normal_odd_order_eq_bot hmin H' hH'normal hCodd
        have hDG' : IsDGroup G :=
          gw_prop9_dGroup_conclusion_from_minimalNormal hmin H' hH'normal hHH hCH
        exact hmin.2.1 hDG'

/-! ## The Section 2 involution-centralizer setup

The setup was originally declared in `Defs`, but its existence proof needs
the centerlessness consequence of Proposition 9.  Keeping the construction
here preserves the acyclic import direction (`Defs` defines the structure;
this module supplies the minimal-counterexample witness).
-/

/-- A minimal counterexample has trivial center.

The center is normal, so simplicity leaves only the bottom/top alternatives.
In the top branch the group is abelian; the quotient by its odd core is then
nilpotent with trivial odd core, hence a `2`-group, making `G` a `D`-group and
contradicting minimality.
-/
private theorem center_eq_bot_of_minimalCounterexample
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    Subgroup.center G = ⊥ := by
  have hsimple : IsSimpleGroup G := minimalCounterexample_isSimple hmin
  let : IsSimpleGroup G := hsimple
  let : (Subgroup.center G).Characteristic := Subgroup.centerCharacteristic
  have hnorm : (Subgroup.center G).Normal := inferInstance
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center G) with hbot | htop
  · exact hbot
  · have hcomm : IsMulCommutative G := Subgroup.center_eq_top_iff.mp htop
    let : CommGroup G := IsMulCommutative.instCommGroup
    let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcorebot : pPrimeCore 2 (G ⧸ pPrimeCore 2 G) = ⊥ :=
      pPrimeCore_quotient_pPrimeCore_eq_bot 2
    have hnil : Group.IsNilpotent (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) := by
      infer_instance
    have htopP : IsPGroup 2 (⊤ : Subgroup (G ⧸ pPrimeCore 2 G)) :=
      isPGroup_of_nilpotent_normal (⊤ : Subgroup (G ⧸ pPrimeCore 2 G))
        inferInstance hnil hcorebot
    have hQ : IsPGroup 2 (G ⧸ pPrimeCore 2 G) :=
      htopP.of_equiv Subgroup.topEquiv
    have hSylow : HasCyclicOrDihedralSylowTwo G := by
      intro S
      rcases hmin.1 S with ⟨m, hm, e⟩
      exact Or.inr ⟨m, hm, e⟩
    exact False.elim (hmin.2.1 (IsDGroup.quotientIsTwoGroup hSylow hQ))

/-- Existence of the notation fixed at the start of Section 2.

The rotation subgroup is transported from a dihedral Sylow model, and the
half-turn supplies the distinguished involution.  The centerlessness lemma
above makes its centralizer proper, after which finite coatomicity supplies
the maximal overgroup `Hhat`.
-/
public theorem exists_centralizerSetup
    {G : Type u} [Group G] [Finite G]
    (hmin : IsMinimalCounterexample G) :
    Nonempty (CentralizerSetup G) := by
  classical
  have hcenter : Subgroup.center G = ⊥ :=
    center_eq_bot_of_minimalCounterexample hmin
  obtain ⟨S⟩ := (Sylow.nonempty (p := 2) (G := G))
  rcases hmin.1 S with ⟨m, hm, he⟩
  rcases he with ⟨e⟩
  let a : ↥S := e.symm (DihedralGroup.r 1)
  let R : Subgroup (↥S) := Subgroup.zpowers a
  let S0 : Subgroup G := R.map (S : Subgroup G).subtype
  have hS0le : S0 ≤ (S : Subgroup G) := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  have hS0cyc : IsCyclic S0 := by
    have hmap : S0 = Subgroup.zpowers ((a : ↥S) : G) := by
      simp [S0, R, a, MonoidHom.map_zpowers]
    rw [hmap]
    exact Subgroup.isCyclic_zpowers _
  have hcardR : Nat.card (↥R) = 2 ^ m := by
    calc
      Nat.card (↥R) = orderOf a := Nat.card_zpowers a
      _ = orderOf (DihedralGroup.r 1) := by
        have heq := e.orderOf_eq a
        simpa [a] using heq
      _ = 2 ^ m := DihedralGroup.orderOf_r_one
  have hcardS0 : Nat.card (↥S0) = 2 ^ m := by
    exact
      (Nat.card_congr
        (Subgroup.equivMapOfInjective R (S : Subgroup G).subtype
          (S : Subgroup G).subtype_injective).toEquiv).symm ▸ hcardR
  have hcardS : Nat.card (↥S) = 2 * 2 ^ m := by
    calc
      Nat.card (↥S) = Nat.card (DihedralGroup (2 ^ m)) := Nat.card_congr e.toEquiv
      _ = 2 * 2 ^ m := DihedralGroup.nat_card
  have hcard : Nat.card (↥S) = 2 * Nat.card (↥S0) := by
    rw [hcardS, hcardS0]
  let tm : DihedralGroup (2 ^ m) :=
    (DihedralGroup.r 1) ^ (2 ^ (m - 1))
  let tS : ↥S := e.symm tm
  let t : G := tS
  have htm_sq : tm ^ 2 = 1 := by
    dsimp [tm]
    calc
      ((DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ (2 ^ (m - 1))) ^ 2 =
          (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ (2 ^ (m - 1) * 2) := by
            rw [pow_mul]
      _ = (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ (2 ^ m) := by
            congr 1
            have hm' : m - 1 + 1 = m := Nat.sub_add_cancel hm
            calc
              2 ^ (m - 1) * 2 = 2 ^ (m - 1 + 1) := by
                rw [pow_succ, Nat.mul_comm]
              _ = 2 ^ m := by rw [hm']
      _ = 1 := by exact DihedralGroup.r_one_pow_n
  have htm_ne : tm ≠ 1 := by
    intro htm1
    have hdvd : 2 ^ m ∣ 2 ^ (m - 1) := by
      have hp : (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ^ (2 ^ (m - 1)) = 1 := by
        simpa [tm] using htm1
      have hdiv : orderOf (DihedralGroup.r 1 : DihedralGroup (2 ^ m)) ∣
          2 ^ (m - 1) := orderOf_dvd_of_pow_eq_one hp
      simpa [DihedralGroup.orderOf_r_one] using hdiv
    have hlt : 2 ^ (m - 1) < 2 ^ m := by
      exact Nat.pow_lt_pow_right (by norm_num : 1 < 2)
        (Nat.sub_lt (by omega) (by omega))
    exact (Nat.not_dvd_of_pos_of_lt (by positivity) hlt) hdvd
  have htS_sq : tS ^ 2 = (1 : ↥S) := by
    simpa [tS] using congrArg e.symm htm_sq
  have htS_ne : tS ≠ 1 := by
    intro h
    have htS1 : tS = (1 : ↥S) := h
    apply htm_ne
    have h' : e tS = e (1 : ↥S) := congrArg e htS1
    simpa [tS] using h'
  have htmemR : tS ∈ R := by
    change e.symm tm ∈ Subgroup.zpowers a
    refine ⟨((2 ^ (m - 1) : ℕ) : ℤ), ?_⟩
    dsimp [a, tm]
    change (e.symm (DihedralGroup.r 1) : ↥S) ^
        ((2 ^ (m - 1) : ℕ) : ℤ) =
      e.symm ((DihedralGroup.r 1) ^ (2 ^ (m - 1)))
    rw [zpow_natCast]
    exact (map_pow (e.symm : DihedralGroup (2 ^ m) →* ↥S)
      (DihedralGroup.r 1) (2 ^ (m - 1))).symm
  have htmemS0 : t ∈ S0 := by
    exact Subgroup.mem_map.mpr ⟨tS, htmemR, rfl⟩
  have ht_ne : t ≠ (1 : G) := by
    intro h
    apply htS_ne
    change (tS : G) = 1 at h
    exact Subtype.ext h
  have ht_sq : t ^ 2 = (1 : G) := congrArg Subtype.val htS_sq
  let hH : Subgroup G := Subgroup.centralizer ({t} : Set G)
  have hHne : hH ≠ ⊤ := by
    intro htop
    have htcenter : t ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hgH : g ∈ hH := by rw [htop]; trivial
      have hgC : g ∈ Subgroup.centralizer ({t} : Set G) := by
        simpa [hH] using hgH
      have hcomm : t * g = g * t :=
        (Subgroup.mem_centralizer_iff.mp hgC) t (by simp)
      exact hcomm.symm
    have htbot : t ∈ (⊥ : Subgroup G) := by
      rw [← hcenter]
      exact htcenter
    exact ht_ne (by simpa using htbot)
  rcases eq_top_or_exists_le_coatom hH with htop | ⟨Hhat, hHhat, hHH⟩
  · exact False.elim (hHne htop)
  · let c : CentralizerSetup G :=
      { S := S
        m := m
        one_le_m := hm
        dihedralEquiv := ⟨e⟩
        S0 := S0
        S0_le_S := hS0le
        S0_cyclic := hS0cyc
        S_index_two := hcard
        t := t
        t_mem_S0 := htmemS0
        t_involution := ⟨ht_ne, ht_sq⟩
        H := hH
        H_eq_centralizer := rfl
        Hhat := Hhat
        H_le_Hhat := hHH
        Hhat_maximal := hHhat }
    exact ⟨c⟩

end

end CFSG.GorensteinWalter
