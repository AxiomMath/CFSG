module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameELeaf
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeTriD4FrameE
public import CFSG.LocalAnalysis.StandardType.GGK0LQD4TwE6

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.PartOne.KD4L CFSG.RankThree.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.StandardType.TablePThreeKG CFSG.RankThree.PartOne.KE6
open CFSG.LieType.Steinberg.TwistedD4 (nd)

open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints frobenius_canonicalRep
  d4Nodes)

open CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple

section


@[expose] noncomputable def rckTriD4_tagE6Equiv (L : Type) [Field L] :
    ModGL TwistTag.E6.tag L ≃* ModGL Tag.E6 L where
  toFun g := g
  invFun g := g
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

@[simp] theorem rckTriD4_tagE6Equiv_apply (L : Type) [Field L]
    (x : ModGL TwistTag.E6.tag L) : rckTriD4_tagE6Equiv L x = x := rfl

@[simp] theorem rckTriD4_tagE6Equiv_symm_apply (L : Type) [Field L]
    (x : ModGL Tag.E6 L) : (rckTriD4_tagE6Equiv L).symm x = x := rfl

@[expose] def rckTriD4_e6GraphPerm : Equiv.Perm (Fin Tag.E6.rank) := TwistTag.E6.perm

theorem rckTriD4_exists_conj_twistedFixed_twist_eq_E6 {L : Type} [Field L] [IsAlgClosed L]
    {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ] (hf : 1 ≤ f)
    {n : ModGL Tag.E6 L} (hn : n ∈ monomialSubgroup Tag.E6 L)
    {π : Equiv.Perm (Fin Tag.E6.rank)}
    (hπ : ∀ i ∈ d4Set Tag.E6, π i ∈ d4Set Tag.E6)
    (hπ' : ∀ i ∈ d4Set Tag.E6, π.symm i ∈ d4Set Tag.E6)
    {u : WeylGroup Tag.E6} (hu : u ∈ parabolicWeylGroup Tag.E6 (d4Set Tag.E6))
    (hact : ∀ j ∈ d4Set Tag.E6, weylQuotientHom Tag.E6 L ⟨n, hn⟩ •
      permLattice rckTriD4_e6GraphPerm (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        u • (Pi.single (π j) 1 : Fin Tag.E6.rank → ℤ)) :
    ∃ n₁ k : ModGL Tag.E6 L, k ∈ subsystemGroup Tag.E6 L (d4Set Tag.E6) ∧
      (∀ j ∈ d4Set Tag.E6, ∀ c : L,
        n₁ * xUnit Tag.E6 L j c * n₁⁻¹ = xUnit Tag.E6 L (π j) c ∧
        n₁ * yUnit Tag.E6 L j c * n₁⁻¹ = yUnit Tag.E6 L (π j) c) ∧
      ∀ g : ModGL Tag.E6 L,
        k * ((n * e6Diagram L) *
            Units.map (entrywiseHom (iterateFrobenius L ℓ f)) g *
            (n * e6Diagram L)⁻¹) * k⁻¹ =
          n₁ * Units.map (entrywiseHom (iterateFrobenius L ℓ f)) (k * g * k⁻¹) * n₁⁻¹ := by
  let b := rckTriD4_tagE6Equiv L
  let uT : WeylGroup TwistTag.E6.tag := u
  let πT : Equiv.Perm (Fin TwistTag.E6.tag.rank) := π
  have hact' : ∀ j ∈ d4Set TwistTag.E6.tag,
      weylQuotientHom TwistTag.E6.tag L ⟨b.symm n, hn⟩ •
        permLattice TwistTag.E6.perm
          (Pi.single j 1 : Fin TwistTag.E6.tag.rank → ℤ) =
          uT • (Pi.single (πT j) 1 : Fin TwistTag.E6.tag.rank → ℤ) := by
    intro j hj
    exact hact j (show j ∈ d4Set Tag.E6 from hj)
  obtain ⟨n₁, k, hk, hgen, heq⟩ :=
    rckTriD4_exists_conj_twistedFixed_twist_eq (L := L) hf (n := b.symm n) hn
      (π := πT) hπ hπ' (u := uT) hu hact'
  refine ⟨b n₁, b k, ?_, ?_, ?_⟩
  · exact hk
  · exact hgen
  · intro g
    exact heq g

theorem rckTriD4Frame_E_twisted {p₀ : ℕ} (S : LangSetup Tag.E6 GGL p₀) {h : ℕ}
    (hq : S.D.q = 2 ^ h)
    (hΦ : ∀ g : ModGL Tag.E6 GGL,
      S.D.Φ g = e6Diagram GGL *
        Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) g *
        (e6Diagram GGL)⁻¹)
    {a : Fin Tag.E6.rank → GGLˣ} (i : KernelComponent (rootCharHom a))
    (v : WeylGroup Tag.E6)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i,
      S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin Tag.E6.rank → ℤ) → _))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2]))
    {w : WeylGroup Tag.E6} (hn : S.D.n = canonicalRep (coxeterSystem Tag.E6) GGL w)
    (hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ) :
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
  haveI : CharP GGL 2 := hℓ2 ▸ hchar
  haveI : Fact (Nat.Prime 2) := ⟨by decide⟩
  obtain ⟨u, hu, w₀, hw₀, πJ, hleaf, hlin, hθ'⟩ :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_tw_action S hρw i v hΨ hρ
  have hπ1 : πJ ≠ 1 :=
    CFSG.LocalAnalysis.GLTheoremA.K155X.l154r4_tw_pi_ne_one S i v hΨ h1 hu hθ'
  have hπ2 : πJ * πJ ≠ 1 :=
    CFSG.StandardType.GGK0LQ.lk0xlqd4tw_pi_sq S i v hΨ hρ h2 hu hleaf hθ'
  have hex : ∃ e ∈ ({1, 2} : Set ℕ), ∀ k : Fin Tag.D4.rank,
      πJ (d4Id (τ := Tag.E6) k) = d4Id (τ := Tag.E6) (rhoE e k) := by
    rcases hleaf.eq_cycle hπ1 hπ2 with hc | hc
    · refine ⟨1, by decide, fun k => ?_⟩
      rw [hc]
      fin_cases k <;> rfl
    · refine ⟨2, by decide, fun k => ?_⟩
      rw [hc]
      fin_cases k <;> rfl
  obtain ⟨e, he_mem, hπe⟩ := hex
  have he : e = 1 ∨ e = 2 := by simpa using he_mem
  let nv : ModGL Tag.E6 GGL := canonicalRep (coxeterSystem Tag.E6) GGL v
  let nw : ModGL Tag.E6 GGL := canonicalRep (coxeterSystem Tag.E6) GGL w
  let nδ : ModGL Tag.E6 GGL := canonicalRep (coxeterSystem Tag.E6) GGL (e6WeylTwist v)
  let n' : ModGL Tag.E6 GGL := nv⁻¹ * nw * nδ
  have hnvM : nv ∈ monomialSubgroup Tag.E6 GGL := canonicalRep_mem_monomialSubgroup GGL v
  have hnwM : nw ∈ monomialSubgroup Tag.E6 GGL := canonicalRep_mem_monomialSubgroup GGL w
  have hnδM : nδ ∈ monomialSubgroup Tag.E6 GGL :=
    canonicalRep_mem_monomialSubgroup GGL (e6WeylTwist v)
  have hn'M : n' ∈ monomialSubgroup Tag.E6 GGL :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hπn' : weylQuotientHom Tag.E6 GGL ⟨n', hn'M⟩ = v⁻¹ * w * e6WeylTwist v := by
    have h1' : (⟨n', hn'M⟩ : monomialSubgroup Tag.E6 GGL) =
        (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 GGL)⁻¹ * ⟨nw, hnwM⟩ *
          ⟨nδ, hnδM⟩ := rfl
    rw [h1', map_mul, map_mul, map_inv,
      weylQuotientHom_eq (mapsRootLines_canonicalRep v),
      weylQuotientHom_eq (mapsRootLines_canonicalRep w),
      weylQuotientHom_eq (mapsRootLines_canonicalRep (e6WeylTwist v))]
  have hnPv : nv⁻¹ * (nw * e6Diagram GGL) * nv = n' * e6Diagram GGL := by
    dsimp only [n']
    have hconj := e6Diagram_conj_canonicalRep (L := GGL) (RingHom.id GGL) v
    have h' : e6Diagram GGL * nv = nδ * e6Diagram GGL := by
      dsimp only [nv, nδ]
      rw [← hconj]
      group
    calc nv⁻¹ * (nw * e6Diagram GGL) * nv
        = nv⁻¹ * nw * (e6Diagram GGL * nv) := by group
      _ = nv⁻¹ * nw * (nδ * e6Diagram GGL) := by rw [h']
      _ = (nv⁻¹ * nw * nδ) * e6Diagram GGL := by group
  have hact : ∀ j ∈ d4Set Tag.E6,
      weylQuotientHom Tag.E6 GGL ⟨n', hn'M⟩ •
        permLattice rckTriD4_e6GraphPerm (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
          u • (Pi.single (πJ j) 1 : Fin Tag.E6.rank → ℤ) := by
    intro j hj
    rw [hπn', hw₀, mul_smul]
    have hlin' : w₀ • permLattice rckTriD4_e6GraphPerm
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ) = permLattice πJ (Pi.single j 1) := by
      simpa [rckTriD4_e6GraphPerm, e6Graph] using hlin (Pi.single j 1)
        (single_mem_parabolicRoots hj)
    rw [hlin', permLattice_single]
  have hπTw : ∀ i ∈ d4Set TwistTag.E6.tag, πJ i ∈ d4Set TwistTag.E6.tag :=
    fun i hi => hleaf.mem_d4Set (show i ∈ d4Set Tag.E6 from hi)
  have hπTw' : ∀ i ∈ d4Set TwistTag.E6.tag, πJ.symm i ∈ d4Set TwistTag.E6.tag :=
    fun i hi => hleaf.inv.mem_d4Set (show i ∈ d4Set Tag.E6 from hi)
  obtain ⟨n₁, k, hk, hgen, heq⟩ :=
    rckTriD4_exists_conj_twistedFixed_twist_eq_E6 (L := GGL) (ℓ := 2) (f := h) hh
      (n := n') hn'M hπTw hπTw' hu hact
  obtain ⟨ε, hεx, hεy⟩ := rckTriD4_d4NativeEquiv (τ := Tag.E6) (L := GGL)
  have hequiv := rckTriD4_d4NativeEquiv_equiv (τ := Tag.E6) (L := GGL) (h := h) (e := e) he
    ε hεx hεy hgen hπe
  let Y : Subgroup (ModGL Tag.E6 GGL) :=
    rootSpan Tag.E6 GGL (componentRoots (rootCharHom a) i)
  let Q : Subgroup (ModGL Tag.E6 GGL) := subsystemGroup Tag.E6 GGL (d4Set Tag.E6)
  have hQeq : Q = rootSpan Tag.E6 GGL (parabolicRoots Tag.E6 (d4Set Tag.E6)) :=
    subsystemGroup_eq_rootSpan (d4Set Tag.E6)
  have hYQ : Q.map (MulAut.conj nv).toMonoidHom = Y := by
    have hYeq : Y = rootSpan Tag.E6 GGL
        ((fun α => v • α) '' parabolicRoots Tag.E6 (d4Nodes Tag.E6)) := by
      dsimp only [Y]
      rw [hΨ]
    rw [hQeq, hYeq]
    exact (canonical_weyl_root_transport Tag.E6 GGL).1 v _ (fun α hα => hα.1)
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
  have hφcoe : ∀ y : Y, (φ y : ModGL Tag.E6 GGL) =
      k * nv⁻¹ * (y : ModGL Tag.E6 GGL) * nv * k⁻¹ := by
    intro y
    rfl
  have hΞcoe : ∀ y : Y, ε (Ξ y) = φ y := fun y => ε.apply_symm_apply (φ y)
  have hYstep : ∀ y ∈ Y, S.D.step y ∈ Y :=
    fun y hy => step_mem_rootSpan S (fun γ hγ => hγ.1.1) hρ hy
  refine ⟨e, he, hYstep, Ξ, ?_, ?_⟩
  · intro y hy
    have hsub : Ξ ⟨S.D.step (y : ModGL Tag.E6 GGL), hYstep y hy⟩ =
        rckTriD4_diagramFrobHom e h (Ξ ⟨y, hy⟩) := by
      apply ε.injective
      rw [hΞcoe]
      have hstep : S.D.step (y : ModGL Tag.E6 GGL) = (nw * e6Diagram GGL) *
          Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) y *
            (nw * e6Diagram GGL)⁻¹ := by
        change S.D.n * S.D.Φ (y : ModGL Tag.E6 GGL) * S.D.n⁻¹ = _
        rw [hn, hΦ (y : ModGL Tag.E6 GGL)]
        dsimp only [nw]
        group
      have hFrnv : Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) nv = nv :=
        frobenius_canonicalRep _ v
      have hq : nv⁻¹ * (y : ModGL Tag.E6 GGL) * nv =
          k⁻¹ * (φ ⟨y, hy⟩ : ModGL Tag.E6 GGL) * k := by
        rw [hφcoe]
        group
      have hFconj : nv⁻¹ * Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) y * nv =
          Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
            (nv⁻¹ * (y : ModGL Tag.E6 GGL) * nv) := by
        rw [map_mul, map_mul, map_inv, hFrnv]
      have hstep' : nv⁻¹ * S.D.step (y : ModGL Tag.E6 GGL) * nv =
          (n' * e6Diagram GGL) *
            Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
              (nv⁻¹ * (y : ModGL Tag.E6 GGL) * nv) * (n' * e6Diagram GGL)⁻¹ := by
        rw [hstep]
        calc nv⁻¹ * ((nw * e6Diagram GGL) *
              Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) y *
              (nw * e6Diagram GGL)⁻¹) * nv
            = (nv⁻¹ * (nw * e6Diagram GGL) * nv) *
                (nv⁻¹ * Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) y * nv) *
                (nv⁻¹ * (nw * e6Diagram GGL) * nv)⁻¹ := by group
          _ = (n' * e6Diagram GGL) *
                Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
                  (nv⁻¹ * (y : ModGL Tag.E6 GGL) * nv) * (n' * e6Diagram GGL)⁻¹ := by
              rw [hnPv, hFconj]
      have hkconj := heq (nv⁻¹ * (y : ModGL Tag.E6 GGL) * nv)
      rw [hq] at hkconj
      have hmain : (φ ⟨S.D.step (y : ModGL Tag.E6 GGL), hYstep y hy⟩ :
          ModGL Tag.E6 GGL) =
          n₁ * Units.map (entrywiseHom (iterateFrobenius GGL 2 h))
            (φ ⟨y, hy⟩ : ModGL Tag.E6 GGL) * n₁⁻¹ := by
        rw [hφcoe]
        rw [show k * nv⁻¹ * S.D.step (y : ModGL Tag.E6 GGL) * nv * k⁻¹ =
            k * (nv⁻¹ * S.D.step (y : ModGL Tag.E6 GGL) * nv) * k⁻¹ from by group]
        rw [hstep', hq]
        simpa [show k * (k⁻¹ * (φ ⟨y, hy⟩ : ModGL Tag.E6 GGL) * k) * k⁻¹ =
            (φ ⟨y, hy⟩ : ModGL Tag.E6 GGL) from by group] using hkconj
      apply Subtype.ext
      rw [hmain]
      rw [show ((φ ⟨y, hy⟩ : Q) : ModGL Tag.E6 GGL) =
          ((ε (Ξ ⟨y, hy⟩) : Q) : ModGL Tag.E6 GGL) from
        congrArg (fun z : Q => (z : ModGL Tag.E6 GGL)) (hΞcoe ⟨y, hy⟩).symm]
      exact hequiv (Ξ ⟨y, hy⟩)
    have hcoe := congrArg (fun z : ↥(adjointGroup Tag.D4 GGL) =>
      (z : ModGL Tag.D4 GGL)) hsub
    rw [hcoe, rckTriD4_diagramFrobHom_coe_triPsi]
  ·
    let z : ModGL Tag.E6 GGL := nv * k⁻¹ * nv⁻¹
    let γ : Fin Tag.E6.rank → ℤ := v • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1
    have hz : z ∈ Y := by
      rw [← hYQ]
      exact ⟨k⁻¹, inv_mem hk, rfl⟩
    have hγ : γ ∈ componentRoots (rootCharHom a) i := by
      rw [hΨ]
      exact ⟨Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1,
        single_mem_parabolicRoots (d4Id_mem (2 : Fin Tag.D4.rank)), rfl⟩
    have pair_iff : ∀ (s : ℤ), s = 1 ∨ s = -1 →
        (∀ y, y ∈ (rootSubgroup Tag.E6 GGL (s • γ)).map (MulAut.conj z).toMonoidHom ↔
          ∃ hy : y ∈ Y, (Ξ ⟨y, hy⟩ : ModGL Tag.D4 GGL) ∈
            rootSubgroup Tag.D4 GGL (s • Pi.single (nd 2) 1)) := by
      intro s hs
      have hεs := rckTriD4_d4NativeEquiv_mem_rootSubgroup_single (τ := Tag.E6) (L := GGL)
        hεx hεy (nd 2) s hs
      have hUsQ : rootSubgroup Tag.E6 GGL (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) ≤ Q := by
        rw [hQeq]
        refine rootSubgroup_le_rootSpan ?_
        rcases hs with rfl | rfl
        · simpa using single_mem_parabolicRoots (d4Id_mem (2 : Fin Tag.D4.rank))
        · simpa using neg_mem_parabolicRoots
            (single_mem_parabolicRoots (d4Id_mem (2 : Fin Tag.D4.rank)))
      have hroot : (rootSubgroup Tag.E6 GGL
          (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1)).map
          (MulAut.conj nv).toMonoidHom = rootSubgroup Tag.E6 GGL (s • γ) := by
        rw [show s • γ = v • (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) from by
          dsimp only [γ]
          exact (smul_comm v s _).symm]
        refine (canonical_weyl_root_transport Tag.E6 GGL).2.1 v _ ?_
        rcases hs with rfl | rfl
        · simpa using isRoot_single Tag.E6 (d4Id (2 : Fin Tag.D4.rank))
        · simpa using IsRoot.neg (isRoot_single Tag.E6 (d4Id (2 : Fin Tag.D4.rank)))
      have hmap_s : (rootSubgroup Tag.E6 GGL (s • γ)).map (MulAut.conj z).toMonoidHom =
          (rootSubgroup Tag.E6 GGL
            (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1)).map
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
        have hφu : (φ ⟨y, hyY⟩ : ModGL Tag.E6 GGL) = u := by
          rw [hφcoe]
          change k * nv⁻¹ * y * nv * k⁻¹ = u
          rw [show y = nv * k⁻¹ * u * k * nv⁻¹ from huy.symm]
          group
        have hεmem : (ε (Ξ ⟨y, hyY⟩) : ModGL Tag.E6 GGL) ∈
            rootSubgroup Tag.E6 GGL (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) := by
          have h1 : (ε (Ξ ⟨y, hyY⟩) : ModGL Tag.E6 GGL) = (φ ⟨y, hyY⟩ : ModGL Tag.E6 GGL) :=
            congrArg Subtype.val (hΞcoe ⟨y, hyY⟩)
          rw [h1, hφu]
          exact hu
        exact (hεs (Ξ ⟨y, hyY⟩)).2 hεmem
      · rintro ⟨hyY, hmem⟩
        rw [hmap_s]
        have hqmem : (φ ⟨y, hyY⟩ : ModGL Tag.E6 GGL) ∈
            rootSubgroup Tag.E6 GGL (s • Pi.single (d4Id (2 : Fin Tag.D4.rank)) 1) := by
          have h1 := (hεs (Ξ ⟨y, hyY⟩)).1 hmem
          rwa [show (ε (Ξ ⟨y, hyY⟩) : ModGL Tag.E6 GGL) = (φ ⟨y, hyY⟩ : ModGL Tag.E6 GGL)
            from congrArg Subtype.val (hΞcoe ⟨y, hyY⟩)] at h1
        refine Subgroup.mem_map.2 ⟨(φ ⟨y, hyY⟩ : ModGL Tag.E6 GGL), hqmem, ?_⟩
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

end

theorem rckTriD4Frame_E
    {τ : Tag} (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) {p₀ : ℕ} (S : LangSetup τ GGL p₀)
    {h : ℕ} (hq : S.D.q = 2 ^ h) {a : Fin τ.rank → GGLˣ}
    (i : KernelComponent (rootCharHom a)) (v : WeylGroup τ)
    (hΨ : componentRoots (rootCharHom a) i =
      (fun α => v • α) '' parabolicRoots τ (d4Nodes τ))
    (hρ : ∀ γ ∈ componentRoots (rootCharHom a) i, S.ρ γ ∈ componentRoots (rootCharHom a) i)
    (h1 : ¬ twistInner (componentRoots (rootCharHom a) i)
      (S.ρ : (Fin τ.rank → ℤ) → _))
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2])) :
    RCKTriD4Frame S (componentRoots (rootCharHom a) i) h := by
  classical
  rcases hτ with rfl | rfl | rfl
  ·
    obtain ⟨Fr, hFr, P, hP, hΦP⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, hPt⟩
    ·
      have hΦunit : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext g
        rw [hΦP g, one_mul, inv_one, mul_one]
      have hFr' : Fr = iterateFrobenius GGL 2 h := by
        ext c
        rw [hFr, hq, iterateFrobenius_def]
      have hΦ' : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) := by
        rw [hFr'] at hΦunit
        exact hΦunit
      obtain ⟨w, hn⟩ := S.D.n_weyl
      have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • γ :=
        fun γ hγ => S.rho_eq_smul_of_frob hFr hΦunit hn hγ
      exact rckTriD4Frame_E_untwisted (τ := Tag.E6) (d4Base_E6) S hq hΦ' i v hΨ hρ h1 h2
        hn hρw
    ·
      cases t
      · have hdiag : diagramAt Tag.E6 GGL TwistTag.E6 ht = e6Diagram GGL := by
          cases ht
          rfl
        have hS : ∃ (t : TwistTag) (h : t.tag = Tag.E6) (Fr : GGL →+* GGL),
            (∀ c, Fr c = c ^ S.D.q) ∧
            ∀ g, S.D.Φ g = diagramAt Tag.E6 GGL t h * Units.map (entrywiseHom Fr) g *
              (diagramAt Tag.E6 GGL t h)⁻¹ :=
          ⟨TwistTag.E6, ht, Fr, hFr, fun g => by rw [← hPt]; exact hΦP g⟩
        obtain ⟨w, hn, hρw⟩ :=
          CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three.KSNotAll24.d4t2out_rho_eq
            S hS
        have hFr' : Fr = iterateFrobenius GGL 2 h := by
          ext c
          rw [hFr, hq, iterateFrobenius_def]
        have hΦP' : ∀ g, S.D.Φ g = P *
            Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) g * P⁻¹ := by
          intro g
          rw [hΦP g, hFr']
        have hΦtw : ∀ g : ModGL Tag.E6 GGL,
            S.D.Φ g = e6Diagram GGL *
              Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) g *
              (e6Diagram GGL)⁻¹ := by
          intro g
          rw [hΦP' g, hPt, hdiag]
        exact rckTriD4Frame_E_twisted S hq hΦtw i v hΨ hρ h1 h2 hn hρw
      · exact absurd ht (by decide)
  ·
    have hne : ∀ t : TwistTag, t.tag ≠ Tag.E7 := by
      intro t
      cases t <;> decide
    obtain ⟨Fr, hFr, hΦunit⟩ := S.D.exists_frob_of_untwisted hne
    have hFr' : Fr = iterateFrobenius GGL 2 h := by
      ext c
      rw [hFr, hq, iterateFrobenius_def]
    have hΦ' : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) := by
      rw [hFr'] at hΦunit
      exact hΦunit
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hρw : ∀ γ, IsRoot Tag.E7 γ → S.ρ γ = w • γ :=
      fun γ hγ => S.rho_eq_smul_of_frob hFr hΦunit hn hγ
    exact rckTriD4Frame_E_untwisted (τ := Tag.E7) (d4Base_E7) S hq hΦ' i v hΨ hρ h1 h2 hn hρw
  ·
    have hne : ∀ t : TwistTag, t.tag ≠ Tag.E8 := by
      intro t
      cases t <;> decide
    obtain ⟨Fr, hFr, hΦunit⟩ := S.D.exists_frob_of_untwisted hne
    have hFr' : Fr = iterateFrobenius GGL 2 h := by
      ext c
      rw [hFr, hq, iterateFrobenius_def]
    have hΦ' : S.D.Φ = Units.map (entrywiseHom (iterateFrobenius GGL 2 h)) := by
      rw [hFr'] at hΦunit
      exact hΦunit
    obtain ⟨w, hn⟩ := S.D.n_weyl
    have hρw : ∀ γ, IsRoot Tag.E8 γ → S.ρ γ = w • γ :=
      fun γ hγ => S.rho_eq_smul_of_frob hFr hΦunit hn hγ
    exact rckTriD4Frame_E_untwisted (τ := Tag.E8) (d4Base_E8) S hq hΦ' i v hΨ hρ h1 h2 hn hρw

end CFSG.StandardType.RCKRP

end
