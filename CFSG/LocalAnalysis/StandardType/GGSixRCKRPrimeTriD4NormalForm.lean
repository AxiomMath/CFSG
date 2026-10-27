module

public import CFSG.HardMathSupport.Timmesfeld.LangTorus.ComponentsExcTw
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcVacuous
public import CFSG.HardMathSupport.Timmesfeld.DefChar.LieOuterE
public import CFSG.HardMathSupport.Timmesfeld.LocalTwo.CrossLin
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.LieType.Simplicity.Finiteness
public import CFSG.LocalAnalysis.ComponentInitial.SylowPointRecovery
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBasic
public import CFSG.Quasithin.Background.A3Structure36BPrime
public import CFSG.RankThree.Chevalley.SteinbergBID4CentralKernel
public import CFSG.RankThree.Lattice.SteinbergBIOrbitQuotFull
public import CFSG.RankThree.PartOne.KE.A1Action
public import CFSG.RankThree.PartOne.KE.A1Levi
public import CFSG.RankThree.PartOne.KE.A1TwistedE6
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.SigmaPerX
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.ThreeA1Group
public import CFSG.RankThree.PartOne.KGD.D4Frame
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.RankThree.PartOne.S8.Statements
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.HardMathSupport.Timmesfeld.CrossChar
  CFSG.RankThree.PartOne.KD4T CFSG.RankThree.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.PartOne.KE (frobenius_canonicalRep d4Nodes)

open CFSG.RankThree.PartOne.KE6 (mapsJ_of_mem_parabolicWeylGroup)



theorem formPerm_leaves_d4Id {τ : Tag} [E6Sub τ] (k : Fin Tag.D4.rank) :
    List.formPerm [e6Idx (τ := τ) 1, e6Idx 2, e6Idx 4] (d4Id k) = d4Id (d4Rho^[1] k) ∧
      List.formPerm [e6Idx (τ := τ) 1, e6Idx 4, e6Idx 2] (d4Id k) = d4Id (d4Rho^[2] k) := by
  have hk : k = 0 ∨ k = 1 ∨ k = 2 ∨ k = 3 := by
    revert k
    decide
  rcases hk with rfl | rfl | rfl | rfl <;>
    refine ⟨?_, ?_⟩ <;>
    apply Fin.ext <;>
    rfl

section NormalForm

variable
  {L : Type} [Field L] [IsAlgClosed L] {p₀ : ℕ}

@[expose] def TriD4NormalForm {τ : Tag} [E6Sub τ] (S : LangSetup τ L p₀) (v : WeylGroup τ)
    (Fr : L →+* L) : Prop :=
  ∃ (u : WeylGroup τ) (t : Fin Tag.D4.rank → Lˣ) (N : ModGL τ L) (e : ℕ),
    u ∈ parabolicWeylGroup τ (d4Set τ) ∧ (e = 1 ∨ e = 2) ∧
    N ∈ Subgroup.normalizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)) ∧
    (∀ (k : Fin Tag.D4.rank) (c : L),
      N * xUnit τ L (d4Id k) c * N⁻¹ = xUnit τ L (d4Id (d4Rho^[e] k)) c) ∧
    (∀ (k : Fin Tag.D4.rank) (c : L),
      N * yUnit τ L (d4Id k) c * N⁻¹ = yUnit τ L (d4Id (d4Rho^[e] k)) c) ∧
    ∀ g : ModGL τ L, (canonicalRep (coxeterSystem τ) L v)⁻¹ *
        S.D.step (canonicalRep (coxeterSystem τ) L v * g * (canonicalRep (coxeterSystem τ) L v)⁻¹) *
        canonicalRep (coxeterSystem τ) L v =
      (canonicalRep (coxeterSystem τ) L u *
          (torusElt τ L (d4Id 0) (t 0) * torusElt τ L (d4Id 1) (t 1) *
            torusElt τ L (d4Id 2) (t 2) * torusElt τ L (d4Id 3) (t 3))⁻¹) *
        (N * Units.map (entrywiseHom Fr) g * N⁻¹) *
        (canonicalRep (coxeterSystem τ) L u *
          (torusElt τ L (d4Id 0) (t 0) * torusElt τ L (d4Id 1) (t 1) *
            torusElt τ L (d4Id 2) (t 2) * torusElt τ L (d4Id 3) (t 3))⁻¹)⁻¹

theorem exists_normalized_explicit {τ : Tag} [E6Sub τ] {n : ModGL τ L}
    (hn : n ∈ monomialSubgroup τ L) {π : Equiv.Perm (Fin τ.rank)}
    (hπ : ∀ i ∈ d4Set τ, π i ∈ d4Set τ) (hπ' : ∀ i ∈ d4Set τ, π.symm i ∈ d4Set τ)
    {u : WeylGroup τ} (hu : u ∈ parabolicWeylGroup τ (d4Set τ))
    (hact : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨n, hn⟩ • (Pi.single j 1 : Fin τ.rank → ℤ) =
      u • (Pi.single (π j) 1 : Fin τ.rank → ℤ)) :
    ∃ (t : Fin Tag.D4.rank → Lˣ) (n₁ : ModGL τ L), n₁ ∈ monomialSubgroup τ L ∧
      n = (canonicalRep (coxeterSystem τ) L u * (d4TorusWord t)⁻¹) * n₁ ∧
      ∀ j ∈ d4Set τ, ∀ c : L,
        n₁ * xUnit τ L j c * n₁⁻¹ = xUnit τ L (π j) c ∧
        n₁ * yUnit τ L j c * n₁⁻¹ = yUnit τ L (π j) c := by
  set w := weylQuotientHom τ L ⟨n, hn⟩ with hw
  set nu := canonicalRep (coxeterSystem τ) L u with hnu
  have hnuQ : nu ∈ subsystemGroup τ L (d4Set τ) := canonicalRep_mem_subsystemGroup hu
  have hnuM : nu ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L u
  have hnuMaps : MapsRootLines nu u := mapsRootLines_canonicalRep u
  set a := nu⁻¹ * n with ha_def
  have haM : a ∈ monomialSubgroup τ L := mul_mem (inv_mem hnuM) hn
  have haMaps : MapsRootLines a (u⁻¹ * w) :=
    hnuMaps.inv.mul (mapsRootLines_weylQuotientHom ⟨n, hn⟩)
  have hae : ∀ j ∈ d4Set τ, (u⁻¹ * w) • (Pi.single j 1 : Fin τ.rank → ℤ) =
      Pi.single (π j) 1 := by
    intro j hj
    rw [mul_smul, hact j hj, inv_smul_smul]
  have hsc : ∀ k : Fin Tag.D4.rank, ∃ r : Lˣ, ∀ c : L,
      a * xUnit τ L (π.symm (d4Id k)) c * a⁻¹ = xUnit τ L (d4Id k) (r * c) ∧
      a * yUnit τ L (π.symm (d4Id k)) c * a⁻¹ =
        yUnit τ L (d4Id k) (((r⁻¹ : Lˣ) : L) * c) :=
    fun k => by
      refine exists_scalars_of_mapsRootLines haM haMaps ?_
      rw [hae _ (hπ' _ (d4Id_mem k)), Equiv.apply_symm_apply]
  choose r hr using hsc
  obtain ⟨t, ht⟩ := exists_d4TorusWord_scalars (τ := τ) (L := L) (fun k => (r k)⁻¹)
  refine ⟨t, d4TorusWord t * a, ?_, ?_, ?_⟩
  · exact mul_mem (Subgroup.mem_sup_left (d4TorusWord_mem_torusGroup t)) haM
  · rw [ha_def]
    group
  · intro j hj c
    obtain ⟨k, hk⟩ := exists_d4Id_eq (hπ j hj)
    have hjk : π.symm (d4Id k) = j := by rw [hk, Equiv.symm_apply_apply]
    obtain ⟨h1x, h1y⟩ := hr k c
    rw [hjk] at h1x h1y
    obtain ⟨h2x, -⟩ := ht k (r k * c)
    obtain ⟨-, h2y⟩ := ht k (((r k)⁻¹ : Lˣ) * c)
    have e1 : (((r k)⁻¹ : Lˣ) : L) * (((r k : Lˣ) : L) * c) = c := by
      rw [← mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mul]
    have e2 : (((r k)⁻¹ : Lˣ)⁻¹ : Lˣ) * (((r k)⁻¹ : Lˣ) * c) = c := by
      rw [inv_inv, ← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
    refine ⟨?_, ?_⟩
    · calc (d4TorusWord t * a) * xUnit τ L j c * (d4TorusWord t * a)⁻¹
          = d4TorusWord t * (a * xUnit τ L j c * a⁻¹) * (d4TorusWord t)⁻¹ := by group
        _ = d4TorusWord t * xUnit τ L (d4Id k) (r k * c) * (d4TorusWord t)⁻¹ := by
              rw [h1x]
        _ = xUnit τ L (d4Id k) c := by rw [h2x, e1]
        _ = xUnit τ L (π j) c := by rw [hk]
    · calc (d4TorusWord t * a) * yUnit τ L j c * (d4TorusWord t * a)⁻¹
          = d4TorusWord t * (a * yUnit τ L j c * a⁻¹) * (d4TorusWord t)⁻¹ := by group
        _ = d4TorusWord t * yUnit τ L (d4Id k) (((r k)⁻¹ : Lˣ) * c) *
              (d4TorusWord t)⁻¹ := by rw [h1y]
        _ = yUnit τ L (d4Id k) c := by rw [h2y, e2]
        _ = yUnit τ L (π j) c := by rw [hk]

theorem exists_triD4_normalForm_untw
    {τ : Tag} [E6Sub τ] (hsearch : D4BaseSearch τ)
    (S : LangSetup τ L p₀) {Fr : L →+* L}
    (hΦ : S.D.Φ = Units.map (entrywiseHom Fr)) {w : WeylGroup τ}
    (hn : S.D.n = canonicalRep (coxeterSystem τ) L w) (hρw : ∀ γ, IsRoot τ γ → S.ρ γ = w • γ)
    {Ψ : Set (Fin τ.rank → ℤ)} (v : WeylGroup τ)
    (hΨ : Ψ = (fun α => v • α) '' parabolicRoots τ (d4Set τ)) (hρ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ)
    (h2 : ¬ twistInner Ψ ((S.ρ : (Fin τ.rank → ℤ) → _)^[2])) :
    TriD4NormalForm S v Fr := by
  classical
  have hroot : ∀ γ ∈ Ψ, IsRoot τ γ := by
    intro γ hγ
    obtain ⟨α, hα, rfl⟩ := hΨ ▸ hγ
    exact IsRoot.smul hα.1 v
  have hw : ∀ γ ∈ Ψ, w • γ ∈ Ψ := fun γ hγ => by
    rw [← hρw γ (hroot γ hγ)]
    exact hρ γ hγ
  have hmaps : CFSG.RankThree.PartOne.KE6.MapsJ τ (d4Set τ) (v⁻¹ * w * v) := by
    intro α hα
    obtain ⟨β, hβ, hβe⟩ := (hΨ ▸ hw (v • α) (hΨ ▸ ⟨α, hα, rfl⟩) :
      w • v • α ∈ (fun α => v • α) '' parabolicRoots τ (d4Set τ))
    rw [mul_smul, mul_smul, ← hβe, inv_smul_smul]
    exact hβ
  obtain ⟨u, hu, w₀, hw₀, π, hπ, hw₀π⟩ := exists_d4_action hsearch hmaps
  have hlin0 : ∀ α ∈ parabolicRoots τ (d4Set τ), w₀ • α = permLattice π α := fun α hα => by
    have := smul_eq_of_simple (w := w₀) (u := 1) (π := π) (J := d4Set τ)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) hα.2
    rwa [one_smul] at this
  have hact : ∀ α ∈ parabolicRoots τ (d4Set τ),
      (v⁻¹ * w * v) • α = u • permLattice π α := fun α hα => by
    rw [hw₀, mul_smul, hlin0 α hα]
  have hπ2 : π * π ≠ 1 := by
    intro hππ
    apply h2
    have hu' : w₀ * u * w₀⁻¹ ∈ parabolicWeylGroup τ (d4Set τ) := by
      have hle : (parabolicWeylGroup τ (d4Set τ)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup τ (d4Set τ) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π j, hπ.mem_d4Set hj, ?_⟩
        change simple τ (π j) = w₀ * simple τ j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨u, hu, rfl⟩
    refine ⟨v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹,
      hΨ ▸ conj_mem_closure_rootReflection v (mul_mem hu hu'), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots τ (d4Set τ))
    have hγr : IsRoot τ (v • α) := hroot _ hγ
    have hw2 : w₀ • w₀ • α = α := by
      have hα' : w₀ • α ∈ parabolicRoots τ (d4Set τ) := by
        rw [hlin0 α hα]
        refine ⟨?_, fun k hk => ?_⟩
        · rw [← hlin0 α hα]
          exact IsRoot.smul hα.1 w₀
        · have hk' : π.symm k ∉ d4Set τ := fun h => hk (by
            have h' := hπ.mem_d4Set (show π.symm k ∈ d4Set τ from h)
            rw [Equiv.apply_symm_apply] at h'
            exact h')
          exact hα.2 _ hk'
      rw [hlin0 _ hα', hlin0 α hα, ← permLattice_mul, hππ]
      rfl
    rw [Function.iterate_succ_apply, Function.iterate_one, hρw _ hγr,
      hρw _ ((isRoot_smul_iff w).2 hγr)]
    calc w • w • v • α = v • ((v⁻¹ * w * v) • (v⁻¹ * w * v) • α) := by
          simp only [mul_smul, smul_inv_smul]
      _ = v • (u • w₀ • u • w₀ • α) := by rw [hw₀]; simp only [mul_smul]
      _ = v • (u • (w₀ * u * w₀⁻¹) • w₀ • w₀ • α) := by simp only [mul_smul, inv_smul_smul]
      _ = (v * (u * (w₀ * u * w₀⁻¹)) * v⁻¹) • v • α := by
          rw [hw2]
          simp only [mul_smul, inv_smul_smul]
  have hπ1 : π ≠ 1 := by
    intro h1
    exact hπ2 (by rw [h1, mul_one])
  set nv := canonicalRep (coxeterSystem τ) L v with hnv
  set nw := canonicalRep (coxeterSystem τ) L w with hnw
  have hnvM : nv ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L v
  have hnwM : nw ∈ monomialSubgroup τ L := canonicalRep_mem_monomialSubgroup L w
  have hn'M : nv⁻¹ * nw * nv ∈ monomialSubgroup τ L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnvM
  have hnvM' : canonicalRep (coxeterSystem τ) L v ∈ monomialSubgroup τ L := by
    rw [← hnv]
    exact hnvM
  have hnwM' : canonicalRep (coxeterSystem τ) L w ∈ monomialSubgroup τ L := by
    rw [← hnw]
    exact hnwM
  have hnvW : weylQuotientHom τ L ⟨nv, hnvM⟩ = v := by
    rw [show (⟨nv, hnvM⟩ : monomialSubgroup τ L) =
      ⟨canonicalRep (coxeterSystem τ) L v, hnvM'⟩ from Subtype.ext hnv]
    exact weylQuotientHom_eq (R := L) (mapsRootLines_canonicalRep (R := L) v)
  have hnwW : weylQuotientHom τ L ⟨nw, hnwM⟩ = w := by
    rw [show (⟨nw, hnwM⟩ : monomialSubgroup τ L) =
      ⟨canonicalRep (coxeterSystem τ) L w, hnwM'⟩ from Subtype.ext hnw]
    exact weylQuotientHom_eq (R := L) (mapsRootLines_canonicalRep (R := L) w)
  have hπn' : weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ = v⁻¹ * w * v := by
    rw [show (⟨nv⁻¹ * nw * nv, hn'M⟩ : monomialSubgroup τ L) =
      (⟨nv, hnvM⟩ : monomialSubgroup τ L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nv, hnvM⟩ from rfl]
    simp only [map_mul, map_inv, hnvW, hnwW]
  have hact' : ∀ j ∈ d4Set τ, weylQuotientHom τ L ⟨nv⁻¹ * nw * nv, hn'M⟩ •
      (Pi.single j 1 : Fin τ.rank → ℤ) = u • (Pi.single (π j) 1 : Fin τ.rank → ℤ) := by
    intro j hj
    rw [hπn', hw₀, mul_smul, hw₀π j hj]
  obtain ⟨t, n₁, hn₁M, hn'eq, hn₁conj⟩ :=
    exists_normalized_explicit hn'M (fun i hi => hπ.mem_d4Set hi)
      (fun i hi => hπ.inv.mem_d4Set hi) hu hact'
  have hNmem : n₁ ∈ Subgroup.normalizer (subsystemGroup τ L (d4Set τ) : Set (ModGL τ L)) :=
    mem_normalizer_subsystemGroup_of_conj (fun i hi => hπ.mem_d4Set hi)
      (fun i hi => hπ.inv.mem_d4Set hi) hn₁conj
  have hstep : ∀ g : ModGL τ L,
      nv⁻¹ * S.D.step (nv * g * nv⁻¹) * nv =
        (canonicalRep (coxeterSystem τ) L u * (d4TorusWord t)⁻¹) *
          (n₁ * Units.map (entrywiseHom Fr) g * n₁⁻¹) *
          (canonicalRep (coxeterSystem τ) L u * (d4TorusWord t)⁻¹)⁻¹ := by
    intro g
    have hΦn : S.D.Φ nv = nv := by
      rw [hΦ]
      exact frobenius_canonicalRep Fr v
    have hstepg : S.D.step (nv * g * nv⁻¹) = nw * (nv * S.D.Φ g * nv⁻¹) * nw⁻¹ := by
      change S.D.n * S.D.Φ (nv * g * nv⁻¹) * S.D.n⁻¹ = _
      rw [hn, map_mul, map_mul, map_inv, hΦn]
    calc nv⁻¹ * S.D.step (nv * g * nv⁻¹) * nv
        = nv⁻¹ * (nw * (nv * S.D.Φ g * nv⁻¹) * nw⁻¹) * nv := by rw [hstepg]
      _ = (nv⁻¹ * nw * nv) * S.D.Φ g * (nv⁻¹ * nw * nv)⁻¹ := by group
      _ = (nv⁻¹ * nw * nv) * Units.map (entrywiseHom Fr) g * (nv⁻¹ * nw * nv)⁻¹ := by
            rw [hΦ]
      _ = ((canonicalRep (coxeterSystem τ) L u * (d4TorusWord t)⁻¹) * n₁) *
            Units.map (entrywiseHom Fr) g *
            ((canonicalRep (coxeterSystem τ) L u * (d4TorusWord t)⁻¹) * n₁)⁻¹ := by
            rw [hn'eq]
      _ = (canonicalRep (coxeterSystem τ) L u * (d4TorusWord t)⁻¹) *
            (n₁ * Units.map (entrywiseHom Fr) g * n₁⁻¹) *
            (canonicalRep (coxeterSystem τ) L u * (d4TorusWord t)⁻¹)⁻¹ := by group
  rcases hπ.eq_cycle hπ1 hπ2 with hπe | hπe
  · subst hπe
    refine ⟨u, t, n₁, 1, hu, Or.inl rfl, hNmem, ?_, ?_, hstep⟩
    · intro k c
      rw [(hn₁conj (d4Id k) (d4Id_mem k) c).1, (formPerm_leaves_d4Id (τ := τ) k).1]
    · intro k c
      rw [(hn₁conj (d4Id k) (d4Id_mem k) c).2, (formPerm_leaves_d4Id (τ := τ) k).1]
  · subst hπe
    refine ⟨u, t, n₁, 2, hu, Or.inr rfl, hNmem, ?_, ?_, hstep⟩
    · intro k c
      rw [(hn₁conj (d4Id k) (d4Id_mem k) c).1, (formPerm_leaves_d4Id (τ := τ) k).2]
    · intro k c
      rw [(hn₁conj (d4Id k) (d4Id_mem k) c).2, (formPerm_leaves_d4Id (τ := τ) k).2]

theorem exists_triD4_normalForm_twE6
    (S : LangSetup Tag.E6 L p₀) {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ S.D.q)
    (hΦ : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹)
    {Ψ : Set (Fin Tag.E6.rank → ℤ)} (v : WeylGroup Tag.E6)
    (hΨ : Ψ = (fun α => v • α) '' parabolicRoots Tag.E6 (d4Set Tag.E6)) (hρ : ∀ γ ∈ Ψ, S.ρ γ ∈ Ψ)
    (h2 : ¬ twistInner Ψ ((S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2])) :
    TriD4NormalForm S v Fr := by
  classical
  obtain ⟨ℓ, f, hℓ, hchar, hf, hq⟩ := S.exists_char_pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have hFr' : Fr = iterateFrobenius L ℓ f := by
    ext x
    rw [hFr, hq, iterateFrobenius_def]
  have hq0 : 0 < S.D.q := by
    rw [hq]
    exact pow_pos hℓ.pos f
  have hFrs : Function.Surjective Fr := fun y => by
    obtain ⟨x, hx⟩ := IsAlgClosed.exists_pow_nat_eq y hq0
    exact ⟨x, by rw [hFr, hx]⟩
  obtain ⟨w, hn⟩ := S.D.n_weyl
  have hρw : ∀ γ, IsRoot Tag.E6 γ → S.ρ γ = w • permLattice e6Graph γ := by
    intro γ hγ
    have hst : S.D.step =
        twFrob TwistTag.E6 (canonicalRep (coxeterSystem TwistTag.E6.tag) L w) Fr := by
      ext1 g
      change S.D.n * S.D.Φ g * S.D.n⁻¹ = canonicalRep (coxeterSystem Tag.E6) L w *
        (e6Diagram L * Units.map (entrywiseHom Fr) g * (e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L w)⁻¹
      rw [hΦ, hn]
    have h2' := map_twFrob_rootSubgroup TwistTag.E6 hFrs w hγ
    have h3 : rootSubgroup Tag.E6 L (S.ρ γ) =
        rootSubgroup Tag.E6 L (w • permLattice e6Graph γ) := by
      rw [← S.frob.map_rootSubgroup γ hγ, hst]
      exact h2'
    have hr : IsRoot Tag.E6 (w • permLattice e6Graph γ) :=
      IsRoot.smul (hγ.permLattice e6Graph_cartan) w
    exact eq_of_rootSubgroup_eq ((S.frob.isRoot_iff γ).2 hγ) hr h3
  have hσσ : ∀ x : Fin Tag.E6.rank → ℤ, permLattice e6Graph (permLattice e6Graph x) = x :=
    fun x => by
      rw [← permLattice_mul, e6Graph_mul_self]
      rfl
  have hσpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6),
      permLattice e6Graph α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6) := by
    intro α hα
    refine ⟨hα.1.permLattice e6Graph_cartan, fun k hk => ?_⟩
    exact hα.2 _ ((e6Graph_on_d4 k).2 hk).1
  have hroot : ∀ γ ∈ Ψ, IsRoot Tag.E6 γ := by
    intro γ hγ
    obtain ⟨α, hα, rfl⟩ := hΨ ▸ hγ
    exact IsRoot.smul hα.1 v
  set w' : WeylGroup Tag.E6 := v⁻¹ * w * e6WeylTwist v with hw'
  have hθ : ∀ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6),
      v⁻¹ • S.ρ (v • α) = w' • permLattice e6Graph α := by
    intro α hα
    rw [hρw _ ((isRoot_smul_iff v).2 hα.1), ← e6WeylTwist_smul v α, hw', mul_smul, mul_smul]
  have hθmem : ∀ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6),
      v⁻¹ • S.ρ (v • α) ∈ parabolicRoots Tag.E6 (d4Set Tag.E6) := by
    intro α hα
    have hmemΨ : v • α ∈ Ψ := by
      rw [hΨ]
      exact ⟨α, hα, rfl⟩
    have h2' := hρ _ hmemΨ
    rw [hΨ] at h2'
    obtain ⟨β, hβ, hβe⟩ := h2'
    rw [← hβe, inv_smul_smul]
    exact hβ
  have hmaps : CFSG.RankThree.PartOne.KE6.MapsJ Tag.E6 (d4Set Tag.E6) w' := by
    intro α hα
    have h1 := hθ (permLattice e6Graph α) (hσpar α hα)
    rw [hσσ] at h1
    rw [← h1]
    exact hθmem _ (hσpar α hα)
  obtain ⟨u, hu, w₀, hw₀, π', hπ', hw₀π⟩ := exists_d4_action d4Base_E6 hmaps
  set πJ : Equiv.Perm (Fin Tag.E6.rank) := π' * Equiv.swap (e6Idx 2) (e6Idx 4) with hπJ
  have hπJleaf : IsD4LeafPerm πJ := isD4LeafPerm_mul_swap hπ'
  have hlin : ∀ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6),
      w₀ • permLattice e6Graph α = permLattice πJ α := by
    intro α hα
    have h1 := smul_eq_of_simple (w := w₀) (u := 1) (π := π') (J := d4Set Tag.E6)
      (fun j hj => by rw [one_smul]; exact hw₀π j hj) (hσpar α hα).2
    rw [one_smul] at h1
    rw [h1, hπJ, permLattice_mul]
    congr 1
    funext k
    simp only [permLattice, Function.comp]
    by_cases hk : 1 ≤ k.val ∧ k.val ≤ 4
    · rw [((e6Graph_on_d4 k).1 hk).2.1]
    · rw [hα.2 _ ((e6Graph_on_d4 k).2 hk).1, hα.2 _ ((e6Graph_on_d4 k).2 hk).2]
  have hθ' : ∀ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6),
      v⁻¹ • S.ρ (v • α) = u • permLattice πJ α := by
    intro α hα
    rw [hθ α hα, hw₀, mul_smul, hlin α hα]
  have hπJpar : ∀ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6),
      permLattice πJ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6) := by
    intro α hα
    have h1 := hθmem α hα
    rw [hθ' α hα] at h1
    have h2' := (mapsJ_of_mem_parabolicWeylGroup (inv_mem hu)) _ h1
    rwa [inv_smul_smul] at h2'
  have hπ2 : πJ * πJ ≠ 1 := by
    intro hππ
    apply h2
    have hδu : e6WeylTwist u ∈ parabolicWeylGroup Tag.E6 (d4Set Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Set Tag.E6)).map e6WeylTwist.toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Set Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨e6Graph j, ((e6Graph_on_d4 j).1 hj).2.2, ?_⟩
        exact (e6WeylTwist_simple j).symm
      exact hle ⟨u, hu, rfl⟩
    have hconj : w₀ * e6WeylTwist u * w₀⁻¹ ∈ parabolicWeylGroup Tag.E6 (d4Set Tag.E6) := by
      have hle : (parabolicWeylGroup Tag.E6 (d4Set Tag.E6)).map (MulAut.conj w₀).toMonoidHom ≤
          parabolicWeylGroup Tag.E6 (d4Set Tag.E6) := by
        rw [parabolicWeylGroup, MonoidHom.map_closure, Subgroup.closure_le]
        rintro _ ⟨_, ⟨j, hj, rfl⟩, rfl⟩
        refine Subgroup.subset_closure ⟨π' j, hπ'.mem_d4Set hj, ?_⟩
        change simple Tag.E6 (π' j) = w₀ * simple Tag.E6 j * w₀⁻¹
        rw [← rootReflection_single, ← rootReflection_eq_conj (hw₀π j hj)]
      exact hle ⟨e6WeylTwist u, hδu, rfl⟩
    obtain ⟨u₂, hu₂⟩ : ∃ x, x = u * (w₀ * e6WeylTwist u * w₀⁻¹) := ⟨_, rfl⟩
    refine ⟨v * u₂ * v⁻¹, hΨ ▸ conj_mem_closure_rootReflection v (hu₂ ▸ mul_mem hu hconj), ?_⟩
    rintro γ hγ
    obtain ⟨α, hα, rfl⟩ := (hΨ ▸ hγ : γ ∈ (fun α => v • α) '' parabolicRoots Tag.E6 (d4Set Tag.E6))
    have hpx : ∀ x ∈ parabolicRoots Tag.E6 (d4Set Tag.E6), permLattice πJ (u • x) =
        (w₀ * e6WeylTwist u * w₀⁻¹) • permLattice πJ x := by
      intro x hx
      rw [← hlin _ (mapsJ_of_mem_parabolicWeylGroup hu x hx), ← hlin x hx,
        ← e6WeylTwist_smul u x, mul_smul, mul_smul, inv_smul_smul]
    set β := u • permLattice πJ α with hβ
    have hβJ : β ∈ parabolicRoots Tag.E6 (d4Set Tag.E6) := by
      rw [hβ, ← hθ' α hα]
      exact hθmem α hα
    have e1 : S.ρ (v • α) = v • β := by
      rw [hβ, ← hθ' α hα, smul_inv_smul]
    have e2 : S.ρ (v • β) = v • (u • permLattice πJ β) := by
      rw [← hθ' β hβJ, smul_inv_smul]
    have e3 : permLattice πJ (permLattice πJ α) = α := by
      rw [← permLattice_mul, hππ]
      rfl
    calc (S.ρ : (Fin Tag.E6.rank → ℤ) → _)^[2] (v • α) = S.ρ (S.ρ (v • α)) := rfl
      _ = v • (u • permLattice πJ β) := by rw [e1, e2]
      _ = v • (u₂ • α) := by
          rw [hβ, hpx _ (hπJpar α hα), e3, hu₂, mul_smul u (w₀ * e6WeylTwist u * w₀⁻¹) α]
      _ = (v * u₂ * v⁻¹) • v • α := by simp only [mul_smul, inv_smul_smul]
  have hπ1 : πJ ≠ 1 := by
    intro h1
    exact hπ2 (by rw [h1, mul_one])
  set nv := canonicalRep (coxeterSystem Tag.E6) L v with hnv
  set nw := canonicalRep (coxeterSystem Tag.E6) L w with hnw
  set nδ := canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v) with hnδ
  have hnvM : nv ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup L v
  have hnwM : nw ∈ monomialSubgroup Tag.E6 L := canonicalRep_mem_monomialSubgroup L w
  have hnδM : nδ ∈ monomialSubgroup Tag.E6 L :=
    canonicalRep_mem_monomialSubgroup L (e6WeylTwist v)
  have hn'M : nv⁻¹ * nw * nδ ∈ monomialSubgroup Tag.E6 L :=
    mul_mem (mul_mem (inv_mem hnvM) hnwM) hnδM
  have hnvW : weylQuotientHom Tag.E6 L ⟨nv, hnvM⟩ = v := by
    rw [show (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L) =
      ⟨canonicalRep (coxeterSystem Tag.E6) L v, by rw [← hnv]; exact hnvM⟩ from
        Subtype.ext hnv]
    exact weylQuotientHom_eq (R := L) (mapsRootLines_canonicalRep (R := L) v)
  have hnwW : weylQuotientHom Tag.E6 L ⟨nw, hnwM⟩ = w := by
    rw [show (⟨nw, hnwM⟩ : monomialSubgroup Tag.E6 L) =
      ⟨canonicalRep (coxeterSystem Tag.E6) L w, by rw [← hnw]; exact hnwM⟩ from
        Subtype.ext hnw]
    exact weylQuotientHom_eq (R := L) (mapsRootLines_canonicalRep (R := L) w)
  have hnδW : weylQuotientHom Tag.E6 L ⟨nδ, hnδM⟩ = e6WeylTwist v := by
    rw [show (⟨nδ, hnδM⟩ : monomialSubgroup Tag.E6 L) =
      ⟨canonicalRep (coxeterSystem Tag.E6) L (e6WeylTwist v),
        by rw [← hnδ]; exact hnδM⟩ from Subtype.ext hnδ]
    exact weylQuotientHom_eq (R := L) (mapsRootLines_canonicalRep (R := L) (e6WeylTwist v))
  have hπn' : weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ = w' := by
    rw [show (⟨nv⁻¹ * nw * nδ, hn'M⟩ : monomialSubgroup Tag.E6 L) =
      (⟨nv, hnvM⟩ : monomialSubgroup Tag.E6 L)⁻¹ * ⟨nw, hnwM⟩ * ⟨nδ, hnδM⟩ from rfl]
    simp only [map_mul, map_inv, hnvW, hnwW, hnδW]
    rfl
  have hnPv : nv⁻¹ * (nw * e6Diagram L) * nv = (nv⁻¹ * nw * nδ) * e6Diagram L := by
    have h := e6Diagram_conj_canonicalRep Fr v
    calc nv⁻¹ * (nw * e6Diagram L) * nv =
        nv⁻¹ * nw * (e6Diagram L * nv * (e6Diagram L)⁻¹) * e6Diagram L := by group
      _ = (nv⁻¹ * nw * nδ) * e6Diagram L := by rw [h]
  have hact : ∀ α ∈ parabolicRoots Tag.E6 (d4Set Tag.E6),
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ • permLattice e6Graph α =
        u • permLattice πJ α := by
    intro α hα
    rw [hπn', hw₀, mul_smul, hlin α hα]
  have hact' : ∀ j ∈ d4Set Tag.E6,
      weylQuotientHom Tag.E6 L ⟨nv⁻¹ * nw * nδ, hn'M⟩ •
        (Pi.single j 1 : Fin Tag.E6.rank → ℤ) =
        u • (Pi.single (π' j) 1 : Fin Tag.E6.rank → ℤ) := by
    intro j hj
    have hσj : permLattice e6Graph (Pi.single j 1) ∈ parabolicRoots Tag.E6 (d4Set Tag.E6) :=
      hσpar _ (single_mem_parabolicRoots hj)
    have h1 := hlin (permLattice e6Graph (Pi.single j 1)) hσj
    rw [hσσ] at h1
    have h := hact (permLattice e6Graph (Pi.single j 1)) hσj
    rw [hσσ] at h
    rw [← h1, hw₀π j hj] at h
    exact h
  obtain ⟨t, n₁, hn₁M, hn'eq, hn₁conj⟩ :=
    exists_normalized_explicit hn'M (fun i hi => hπ'.mem_d4Set hi)
      (fun i hi => hπ'.inv.mem_d4Set hi) hu hact'
  have hNx : ∀ j ∈ d4Set Tag.E6, ∀ c : L,
      (n₁ * e6Diagram L) * xUnit Tag.E6 L j c * (n₁ * e6Diagram L)⁻¹
        = xUnit Tag.E6 L (πJ j) c := by
    intro j hj c
    have hσjJ : e6Graph j ∈ d4Set Tag.E6 := ((e6Graph_on_d4 j).1 hj).2.2
    have hdiag : e6Diagram L * xUnit Tag.E6 L j c * (e6Diagram L)⁻¹ =
        xUnit Tag.E6 L (e6Graph j) c :=
      diagramMap_mul_xUnit_mul_inv (K := L) (t := TwistTag.E6) j c
    calc (n₁ * e6Diagram L) * xUnit Tag.E6 L j c * (n₁ * e6Diagram L)⁻¹
        = n₁ * (e6Diagram L * xUnit Tag.E6 L j c * (e6Diagram L)⁻¹) * n₁⁻¹ := by group
      _ = n₁ * xUnit Tag.E6 L (e6Graph j) c * n₁⁻¹ := by rw [hdiag]
      _ = xUnit Tag.E6 L (π' (e6Graph j)) c := (hn₁conj (e6Graph j) hσjJ c).1
      _ = xUnit Tag.E6 L (πJ j) c := by
            rw [((e6Graph_on_d4 j).1 hj).1]
            rfl
  have hNy : ∀ j ∈ d4Set Tag.E6, ∀ c : L,
      (n₁ * e6Diagram L) * yUnit Tag.E6 L j c * (n₁ * e6Diagram L)⁻¹
        = yUnit Tag.E6 L (πJ j) c := by
    intro j hj c
    have hσjJ : e6Graph j ∈ d4Set Tag.E6 := ((e6Graph_on_d4 j).1 hj).2.2
    have hdiag : e6Diagram L * yUnit Tag.E6 L j c * (e6Diagram L)⁻¹ =
        yUnit Tag.E6 L (e6Graph j) c :=
      diagramMap_mul_yUnit_mul_inv (K := L) (t := TwistTag.E6) j c
    calc (n₁ * e6Diagram L) * yUnit Tag.E6 L j c * (n₁ * e6Diagram L)⁻¹
        = n₁ * (e6Diagram L * yUnit Tag.E6 L j c * (e6Diagram L)⁻¹) * n₁⁻¹ := by group
      _ = n₁ * yUnit Tag.E6 L (e6Graph j) c * n₁⁻¹ := by rw [hdiag]
      _ = yUnit Tag.E6 L (π' (e6Graph j)) c := (hn₁conj (e6Graph j) hσjJ c).2
      _ = yUnit Tag.E6 L (πJ j) c := by
            rw [((e6Graph_on_d4 j).1 hj).1]
            rfl
  have hNconj : ∀ j ∈ d4Set Tag.E6, ∀ c : L,
      (n₁ * e6Diagram L) * xUnit Tag.E6 L j c * (n₁ * e6Diagram L)⁻¹ =
        xUnit Tag.E6 L (πJ j) c ∧
      (n₁ * e6Diagram L) * yUnit Tag.E6 L j c * (n₁ * e6Diagram L)⁻¹ =
        yUnit Tag.E6 L (πJ j) c :=
    fun j hj c => ⟨hNx j hj c, hNy j hj c⟩
  have hNmem : n₁ * e6Diagram L ∈
      Subgroup.normalizer (subsystemGroup Tag.E6 L (d4Set Tag.E6) : Set (ModGL Tag.E6 L)) :=
    mem_normalizer_subsystemGroup_of_conj (fun i hi => hπJleaf.mem_d4Set hi)
      (fun i hi => hπJleaf.inv.mem_d4Set hi) hNconj
  have hstep : ∀ g : ModGL Tag.E6 L,
      nv⁻¹ * S.D.step (nv * g * nv⁻¹) * nv =
        (canonicalRep (coxeterSystem Tag.E6) L u * (d4TorusWord t)⁻¹) *
          ((n₁ * e6Diagram L) * Units.map (entrywiseHom Fr) g * (n₁ * e6Diagram L)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) L u * (d4TorusWord t)⁻¹)⁻¹ := by
    intro g
    have hPnv : Units.map (entrywiseHom Fr) nv = nv := frobenius_canonicalRep Fr v
    have hstepg : S.D.step (nv * g * nv⁻¹) =
        nw * (e6Diagram L * (nv * Units.map (entrywiseHom Fr) g * nv⁻¹) *
          (e6Diagram L)⁻¹) * nw⁻¹ := by
      change S.D.n * S.D.Φ (nv * g * nv⁻¹) * S.D.n⁻¹ = _
      rw [hn, hΦ, map_mul, map_mul, map_inv, hPnv]
    calc nv⁻¹ * S.D.step (nv * g * nv⁻¹) * nv
        = nv⁻¹ * (nw * (e6Diagram L * (nv * Units.map (entrywiseHom Fr) g * nv⁻¹) *
            (e6Diagram L)⁻¹) * nw⁻¹) * nv := by rw [hstepg]
      _ = (nv⁻¹ * (nw * e6Diagram L) * nv) * Units.map (entrywiseHom Fr) g *
            (nv⁻¹ * (nw * e6Diagram L) * nv)⁻¹ := by group
      _ = ((nv⁻¹ * nw * nδ) * e6Diagram L) * Units.map (entrywiseHom Fr) g *
            (((nv⁻¹ * nw * nδ) * e6Diagram L))⁻¹ := by rw [hnPv]
      _ = (((canonicalRep (coxeterSystem Tag.E6) L u * (d4TorusWord t)⁻¹) * n₁) *
            e6Diagram L) * Units.map (entrywiseHom Fr) g *
            ((((canonicalRep (coxeterSystem Tag.E6) L u * (d4TorusWord t)⁻¹) * n₁) *
              e6Diagram L))⁻¹ := by rw [hn'eq]
      _ = (canonicalRep (coxeterSystem Tag.E6) L u * (d4TorusWord t)⁻¹) *
            ((n₁ * e6Diagram L) * Units.map (entrywiseHom Fr) g * (n₁ * e6Diagram L)⁻¹) *
            (canonicalRep (coxeterSystem Tag.E6) L u * (d4TorusWord t)⁻¹)⁻¹ := by group
  rcases hπJleaf.eq_cycle hπ1 hπ2 with hπJe | hπJe
  · rw [hπJe] at hNx hNy
    refine ⟨u, t, n₁ * e6Diagram L, 1, hu, Or.inl rfl, hNmem, ?_, ?_, hstep⟩
    · intro k c
      rw [hNx (d4Id k) (d4Id_mem k) c, (formPerm_leaves_d4Id (τ := Tag.E6) k).1]
    · intro k c
      rw [hNy (d4Id k) (d4Id_mem k) c, (formPerm_leaves_d4Id (τ := Tag.E6) k).1]
  · rw [hπJe] at hNx hNy
    refine ⟨u, t, n₁ * e6Diagram L, 2, hu, Or.inr rfl, hNmem, ?_, ?_, hstep⟩
    · intro k c
      rw [hNx (d4Id k) (d4Id_mem k) c, (formPerm_leaves_d4Id (τ := Tag.E6) k).2]
    · intro k c
      rw [hNy (d4Id k) (d4Id_mem k) c, (formPerm_leaves_d4Id (τ := Tag.E6) k).2]

theorem exists_triD4_normalForm
    {τ : Tag} [E6Sub τ]
    (hτ : τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (S : LangSetup τ L p₀) {a : Fin τ.rank → Lˣ}
    (hT : rootDiagUnit τ a ∈ S.D.torus) {p : ℕ} (hp : p.Prime) (hpL : (p : L) ≠ 0)
    (hTp : rootDiagUnit τ a ^ p = 1) (i : KernelComponent (rootCharHom a))
    (hr : compRank (componentRoots (rootCharHom a) i) = 4)
    (hc : (componentRoots (rootCharHom a) i).ncard = 24)
    (h2 : ¬ twistInner (componentRoots (rootCharHom a) i)
      ((S.ρ : (Fin τ.rank → ℤ) → _)^[2 * componentOrbitLength S.ρ
        (componentRoots (rootCharHom a) i)])) :
    componentOrbitLength S.ρ (componentRoots (rootCharHom a) i) = 1 ∧
      ∃ (v : WeylGroup τ) (Fr : L →+* L), (∀ c, Fr c = c ^ S.D.q) ∧
        componentRoots (rootCharHom a) i = (fun α => v • α) '' parabolicRoots τ (d4Set τ) ∧
        TriD4NormalForm S v Fr := by
  classical
  rcases hτ with rfl | rfl | rfl
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E6 kacCount_E6_four (by decide)
      (by decide)
      (fun y hy => far_d4_E6 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨none, by decide⟩ (lt_of_eq_of_lt kacCount_far_E6 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    rw [hs, mul_one] at h2
    obtain ⟨Fr, hFr, P, hP, hΦ⟩ := S.D.steinberg
    rcases hP with rfl | ⟨t, ht, rfl⟩
    · have hΦ' : S.D.Φ = Units.map (entrywiseHom Fr) := by
        ext1 g
        rw [hΦ, one_mul, inv_one, mul_one]
      obtain ⟨w, hn⟩ := S.D.n_weyl
      exact ⟨hs, v, Fr, hFr, hv,
        exists_triD4_normalForm_untw d4Base_E6 S hΦ' hn
          (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ' hn hγ) v hv hρ h2⟩
    · cases t with
      | D4 => exact absurd ht (by decide)
      | E6 =>
        have hΦ' : ∀ g, S.D.Φ g = e6Diagram L * Units.map (entrywiseHom Fr) g *
            (e6Diagram L)⁻¹ := hΦ
        exact ⟨hs, v, Fr, hFr, hv,
          exists_triD4_normalForm_twE6 S hFr hΦ' v hv hρ h2⟩
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E7 kacCount_E7_four (by decide)
      (by decide)
      (fun y hy => far_d4_E7 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E7 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    rw [hs, mul_one] at h2
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E7
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ⟨hs, v, Fr, hFr, hv,
      exists_triD4_normalForm_untw d4Base_E7 S hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) v hv hρ h2⟩
  · obtain ⟨v, hv, hρ⟩ := S.d4_pinnedT_of_prime hp hpL facts_E8 kacCount_E8_four (by decide)
      (by decide)
      (fun y hy => far_d4_E8 y fun z hz => by
        have h := hy z hz
        rwa [KacData.Adj, extRoot_eq_extRootOf] at h)
      ⟨some 0, by decide⟩ (lt_of_eq_of_lt kacCount_far_E8 (by decide)) hT hTp i hr hc
    have hfin : (componentRoots (rootCharHom a) i).Finite :=
      (finite_setOf_isRoot _).subset fun γ hγ => hγ.1.1
    have hs := componentOrbitLength_eq_one hfin hρ
    rw [hs, mul_one] at h2
    obtain ⟨Fr, hFr, hΦ⟩ := S.D.exists_frob_of_untwisted twistTag_tag_ne_E8
    obtain ⟨w, hn⟩ := S.D.n_weyl
    exact ⟨hs, v, Fr, hFr, hv,
      exists_triD4_normalForm_untw d4Base_E8 S hΦ hn
        (fun γ hγ => S.rho_eq_smul_of_frob hFr hΦ hn hγ) v hv hρ h2⟩

end NormalForm

end CFSG.StandardType.RCKRP

