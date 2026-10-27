module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameE
public import CFSG.LocalAnalysis.StandardType.GGK0LQD4TwE6
public import CFSG.LocalAnalysis.StandardType.GGTablePThreeE6RatLabelOuterD
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.ExcLang
public import CFSG.LieType.Chevalley.E7SupportedBruhat

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TablePThreeKG
open CFSG.LieType.Steinberg.TwistedD4 (nd)

open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple


theorem rckTriD4Frame_E_untwisted {τ : Tag} [E6Sub τ]
    (hsearch : D4BaseSearch τ) {p₀ : ℕ} (S : LangSetup τ GGL p₀) {h : ℕ}
    (hq : S.D.q = 2 ^ h)
    (hΦ : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius GGL 2 h)))
    {a : Fin τ.rank → GGLˣ} (i : KernelComponent (rootCharHom a))
    (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin τ.rank → ℤ) → _))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2]))
    {w : WeylGroup τ} (hn : S.D.n = canonicalRep (coxeterSystem τ) GGL w)
    (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ) :
    RCKTriD4Frame S (componentRoots (rootCharHom a) i) h := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq'⟩ := S.exists_char_pow
  have hℓ2 : ℓ = 2 := by
    have hpow : ℓ ^ f = 2 ^ h := hq'.symm.trans hq
    have hdvd : ℓ ∣ 2 ^ h := by
      rw [← hpow]
      exact dvd_pow_self ℓ (Nat.pos_iff_ne_zero.mp hf)
    have hdvd2 : ℓ ∣ 2 := hℓ.dvd_of_dvd_pow hdvd
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd2 with h1 | h2
    · exact absurd h1 hℓ.ne_one
    · exact h2
  have hq'' : S.D.q = 2 ^ f := by rwa [hℓ2] at hq'
  have hfh : f = h := Nat.pow_right_injective (le_refl 2) (hq''.symm.trans hq)
  have hh : 1 ≤ h := hfh ▸ hf
  obtain ⟨u, hu, π, hleaf, hπ1, hπ2, hact⟩ :=
    CFSG.StandardType.TablePThreeKG.d4_action_pi_sq hsearch S hρw i v hΨ hρ h1 h2
  have hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ := fun i hi => hleaf.mem_d4Set hi
  have hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ := fun i hi => hleaf.inv.mem_d4Set hi
  have hex : ∃ e ∈ ({1, 2} : Set ℕ), ∀ k : Fin Tag.D4.rank,
      π (d4Id k) = d4Id (rhoE e k) := by
    rcases hleaf.eq_cycle hπ1 hπ2 with hc | hc
    · refine ⟨1, by decide, fun k => ?_⟩
      rw [hc]
      fin_cases k <;> rfl
    · refine ⟨2, by decide, fun k => ?_⟩
      rw [hc]
      fin_cases k <;> rfl
  obtain ⟨e, he_mem, hπe⟩ := hex
  have he : e = 1 ∨ e = 2 := by simpa using he_mem
  let nv : ModGL τ GGL := canonicalRep (coxeterSystem τ) GGL v
  let nw : ModGL τ GGL := canonicalRep (coxeterSystem τ) GGL w
  let n' : ModGL τ GGL := nv⁻¹ * nw * nv
  have hnvM : nv ∈ monomialSubgroup τ GGL := canonicalRep_mem_monomialSubgroup GGL v
  have hnwM : nw ∈ monomialSubgroup τ GGL := canonicalRep_mem_monomialSubgroup GGL w
  have hn'M : n' ∈ monomialSubgroup τ GGL :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hn'w : weylQuotientHom τ GGL ⟨n', hn'M⟩ = v⁻¹ * w * v := by
    have h1 : (⟨n', hn'M⟩ : monomialSubgroup τ GGL) =
        (⟨nv, hnvM⟩ : monomialSubgroup τ GGL)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ := rfl
    rw [h1, map_mul, map_mul, map_inv, weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w)]
  have hn'act : ∀ j ∈ d4Set τ, weylQuotientHom τ GGL ⟨n', hn'M⟩ •
      (Pi.single j 1 : Fin τ.rank → ℤ) = u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := by
    intro j hj
    rw [hn'w, hact (Pi.single j 1) (single_mem_parabolicRoots hj), permLattice_single]
  haveI : CharP GGL 2 := hℓ2 ▸ hchar
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨n₁, k, hk, hgen, heq⟩ :=
    rckTriD4_exists_conj_twistedFixed_eq (τ := τ) (L := GGL) (ℓ := 2) (f := h) hh
      (n := n') hn'M hπ hπ' hu hn'act
  obtain ⟨ε, hεx, hεy⟩ := rckTriD4_d4NativeEquiv (τ := τ) (L := GGL)
  have hequiv := rckTriD4_d4NativeEquiv_equiv (τ := τ) (L := GGL) (h := h) (e := e) he
    ε hεx hεy hgen hπe
  let Y : Subgroup (ModGL τ GGL) := rootSpan τ GGL (componentRoots (rootCharHom a) i)
  let Q : Subgroup (ModGL τ GGL) := subsystemGroup τ GGL (d4Set τ)
  have hQeq : Q = rootSpan τ GGL (parabolicRoots τ (d4Set τ)) :=
    subsystemGroup_eq_rootSpan (d4Set τ)
  have hYQ : Q.map (MulAut.conj nv).toMonoidHom = Y := by
    have hYeq : Y = rootSpan τ GGL ((fun α => v • α) '' parabolicRoots τ (d4Nodes τ)) := by
      dsimp only [Y]
      rw [hΨ]
    rw [hQeq, hYeq]
    exact (canonical_weyl_root_transport τ GGL).1 v _ (fun α hα => hα.1)
  have hkQ : k ∈ Q := hk
  have hQmap : Q.map (MulAut.conj k).toMonoidHom = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hkQ)
  have hmap : Y.map (MulAut.conj (k * nv⁻¹)).toMonoidHom = Q := by
    rw [← hYQ, Subgroup.map_map]
    have hcomp : (MulAut.conj (k * nv⁻¹)).toMonoidHom.comp
        (MulAut.conj nv).toMonoidHom = (MulAut.conj k).toMonoidHom := by
      ext x
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
        mul_inv_rev, inv_inv]
      group
    rw [hcomp, hQmap]
  let φ : Y ≃* Q :=
    ((Y.equivMapOfInjective (MulAut.conj (k * nv⁻¹)).toMonoidHom
      (MulAut.conj (k * nv⁻¹)).injective).trans (MulEquiv.subgroupCongr hmap))
  let Ξ : Y ≃* ↥(adjointGroup Tag.D4 GGL) := φ.trans ε.symm
  have hφcoe : ∀ y : Y, (φ y : ModGL τ GGL) =
      k * nv⁻¹ * (y : ModGL τ GGL) * nv * k⁻¹ := by
    intro y
    rfl
  have hΞcoe : ∀ y : Y, ε (Ξ y) = φ y := fun y => ε.apply_symm_apply (φ y)
  have hYstep : ∀ y ∈ Y, S.D.step y ∈ Y :=
    fun y hy => step_mem_rootSpan S (fun γ hγ => hγ.1.1) hρ hy
  refine ⟨e, he, hYstep, Ξ, ?_, ?_⟩
  · intro y hy
    have hsub : Ξ ⟨S.D.step (y : ModGL τ GGL), hYstep y hy⟩ =
        rckTriD4_diagramFrobHom e h (Ξ ⟨y, hy⟩) := by
      apply ε.injective
      rw [hΞcoe]
      have hstep : S.D.step (y : ModGL τ GGL) = nw * Units.map
          (entrywiseHom (iterateFrobenius GGL 2 h)) y * nw⁻¹ := by
        change S.D.n * S.D.Φ y * S.D.n⁻¹ = _
        rw [hn, hΦ]
      have hFrnv : Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) nv = nv :=
        frobenius_canonicalRep _ v
      have hq : nv⁻¹ * (y : ModGL τ GGL) * nv =
          k⁻¹ * (φ ⟨y, hy⟩ : ModGL τ GGL) * k := by
        rw [hφcoe]
        group
      have hstep' : nv⁻¹ * S.D.step (y : ModGL τ GGL) * nv =
          n' * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
            (nv⁻¹ * (y : ModGL τ GGL) * nv) * n'⁻¹ := by
        rw [hstep]
        dsimp only [n']
        rw [map_mul, map_mul, map_inv, hFrnv]
        group
      have hkconj := heq (nv⁻¹ * (y : ModGL τ GGL) * nv)
      rw [hq] at hkconj
      have hmain : (φ ⟨S.D.step (y : ModGL τ GGL), hYstep y hy⟩ : ModGL τ GGL) =
          n₁ * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
            (φ ⟨y, hy⟩ : ModGL τ GGL) * n₁⁻¹ := by
        rw [hφcoe]
        rw [show k * nv⁻¹ * S.D.step (y : ModGL τ GGL) * nv * k⁻¹ =
            k * (nv⁻¹ * S.D.step (y : ModGL τ GGL) * nv) * k⁻¹ from by group]
        rw [hstep', hq]
        simpa [show k * (k⁻¹ * (φ ⟨y, hy⟩ : ModGL τ GGL) * k) * k⁻¹ =
            (φ ⟨y, hy⟩ : ModGL τ GGL) from by group] using hkconj
      apply Subtype.ext
      rw [hmain]
      rw [show ((φ ⟨y, hy⟩ : Q) : ModGL τ GGL) =
          ((ε (Ξ ⟨y, hy⟩) : Q) : ModGL τ GGL) from
        congrArg (fun z : Q => (z : ModGL τ GGL)) (hΞcoe ⟨y, hy⟩).symm]
      exact hequiv (Ξ ⟨y, hy⟩)
    have hcoe : ((Ξ ⟨S.D.step (y : ModGL τ GGL), hYstep y hy⟩ :
        ↥(adjointGroup Tag.D4 GGL)) : ModGL Tag.D4 GGL) =
        ((rckTriD4_diagramFrobHom e h (Ξ ⟨y, hy⟩) :
          ↥(adjointGroup Tag.D4 GGL)) : ModGL Tag.D4 GGL) :=
      congrArg (fun z : ↥(adjointGroup Tag.D4 GGL) => (z : ModGL Tag.D4 GGL)) hsub
    rw [hcoe, rckTriD4_diagramFrobHom_coe_triPsi]
  ·
    let z : ModGL τ GGL := nv * k⁻¹ * nv⁻¹
    let γ : Fin τ.rank → ℤ := v • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1
    have hz : z ∈ Y := by
      rw [← hYQ]
      exact ⟨k⁻¹, inv_mem hk, rfl⟩
    have hγ : γ ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1,
        single_mem_parabolicRoots (d4Id_mem (2 : Fin Tag.D4.rank)), rfl⟩
    have pair_iff : ∀ (s : ℤ), s = 1 ∨ s = -1 →
        (∀ y, y ∈ (rootSubgroup τ GGL (s • γ)).map (MulAut.conj z).toMonoidHom ↔
          ∃ hy : y ∈ Y, (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈
            rootSubgroup Tag.D4 GGL (s • Pi.single (nd 2) 1)) := by
      intro s hs
      have hεs := rckTriD4_d4NativeEquiv_mem_rootSubgroup_single (τ := τ) (L := GGL)
        hεx hεy (nd 2) s hs
      have hUsQ : rootSubgroup τ GGL (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) ≤ Q := by
        rw [hQeq]
        refine rootSubgroup_le_rootSpan ?_
        rcases hs with rfl | rfl
        · simpa using single_mem_parabolicRoots (d4Id_mem (2 : Fin Tag.D4.rank))
        · simpa using neg_mem_parabolicRoots
            (single_mem_parabolicRoots (d4Id_mem (2 : Fin Tag.D4.rank)))
      have hroot : (rootSubgroup τ GGL
          (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1)).map
          (MulAut.conj nv).toMonoidHom = rootSubgroup τ GGL (s • γ) := by
        rw [show s • γ = v • (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) from by
          dsimp only [γ]
          exact (smul_comm v s _).symm]
        refine (canonical_weyl_root_transport τ GGL).2.1 v _ ?_
        rcases hs with rfl | rfl
        · simpa using isRoot_single τ (d4Id (2 : Fin Tag.D4.rank))
        · simpa using IsRoot.neg (isRoot_single τ (d4Id (2 : Fin Tag.D4.rank)))
      have hmap_s : (rootSubgroup τ GGL (s • γ)).map (MulAut.conj z).toMonoidHom =
          (rootSubgroup τ GGL (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1)).map
            (MulAut.conj (nv * k⁻¹)).toMonoidHom := by
        rw [← hroot, Subgroup.map_map]
        congr 1
        ext x
        dsimp only [z]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          mul_inv_rev, inv_inv]
        group
      intro y
      constructor
      · intro hy
        rw [hmap_s] at hy
        obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.1 hy
        have huQ : u ∈ Q := hUsQ hu
        have hyY : y ∈ Y := by
          rw [← hYQ]
          refine Subgroup.mem_map.2 ⟨k⁻¹ * u * k,
            mul_mem (mul_mem (inv_mem hkQ) huQ) hkQ, ?_⟩
          rw [← huy]
          simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
            mul_inv_rev, inv_inv]
          group
        refine ⟨hyY, ?_⟩
        have hφu : (φ ⟨y, hyY⟩ : ModGL τ GGL) = u := by
          rw [hφcoe]
          change k * nv⁻¹ * y * nv * k⁻¹ = u
          rw [show y = nv * k⁻¹ * u * k * nv⁻¹ from huy.symm]
          group
        have hεmem : (ε (Ξ ⟨y, hyY⟩) : ModGL τ GGL) ∈
            rootSubgroup τ GGL (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) := by
          have h1 : (ε (Ξ ⟨y, hyY⟩) : ModGL τ GGL) = (φ ⟨y, hyY⟩ : ModGL τ GGL) :=
            congrArg Subtype.val (hΞcoe ⟨y, hyY⟩)
          rw [h1, hφu]
          exact hu
        exact (hεs (Ξ ⟨y, hyY⟩)).2 hεmem
      · rintro ⟨hyY, hmem⟩
        rw [hmap_s]
        have hqmem : (φ ⟨y, hyY⟩ : ModGL τ GGL) ∈
            rootSubgroup τ GGL (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) := by
          have h1 := (hεs (Ξ ⟨y, hyY⟩)).1 hmem
          rwa [show (ε (Ξ ⟨y, hyY⟩) : ModGL τ GGL) = (φ ⟨y, hyY⟩ : ModGL τ GGL)
            from congrArg Subtype.val (hΞcoe ⟨y, hyY⟩)] at h1
        refine Subgroup.mem_map.2 ⟨(φ ⟨y, hyY⟩ : ModGL τ GGL), hqmem, ?_⟩
        rw [hφcoe]
        simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
          mul_inv_rev, inv_inv]
        group
    refine Exists.intro z ?_
    refine ⟨hz, ?_⟩
    refine Exists.intro γ ?_
    refine ⟨hγ, ?_⟩
    refine ⟨?_, ?_⟩
    · rw [show γ = (1 : ℤ) • γ from (one_smul ℤ γ).symm,
          show (Pi.single (nd 2) 1 : Fin Tag.D4.rank → ℤ) =
            (1 : ℤ) • (Pi.single (nd 2) 1 : Fin Tag.D4.rank → ℤ) from
            (one_smul ℤ _).symm]
      exact pair_iff 1 (Or.inl rfl)
    · rw [show -γ = (-1 : ℤ) • γ from (neg_one_smul ℤ γ).symm,
          show (-Pi.single (nd 2) 1 : Fin Tag.D4.rank → ℤ) =
            (-1 : ℤ) • (Pi.single (nd 2) 1 : Fin Tag.D4.rank → ℤ) from
            (neg_one_smul ℤ _).symm]
      exact pair_iff (-1) (Or.inr rfl)


end CFSG.StandardType.RCKRP

end
