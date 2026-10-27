module

public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberOrthogonal
public import CFSG.LocalAnalysis.StandardType.GGOrdinaryMemberE7RootRecognition
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterInvLangSetup
public import Certificates.Certificate1952
import CFSG.LocalAnalysis.StandardType.GGLieCoreToralInd
import CFSG.RankThree.PartOne.KE6.EqpA24
import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBLang
import CFSG.GroupTheory.ElemAbelianClosure
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.StandardType.GGStdPosRootKerForm
import CFSG.LieType.SeitzGeneration.ExcTorusCount

public noncomputable section

set_option autoImplicit false

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Exceptional
  CFSG.SeitzReduction.E8Pilot
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.AlgebraicGroups
  CFSG.LieType.CurtisTits
  CFSG.RankThree.PartTwo.Sec21 CFSG.LocalAnalysis.ComponentInitial
  CFSG.HardMathSupport.Timmesfeld.LangTorus

theorem rho_eq_neg_of_full_torsion_torus_E7
    {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (S : LangSetup .E7 L 5)
    (hfull : ∀ a : Fin (Tag.rank .E7) → Lˣ, (∀ i, a i ^ p = 1) →
      rootDiagUnit .E7 a ∈ S.D.torus)
    (hplus : p ∣ S.D.q + 1) :
    ∀ gamma, IsRoot .E7 gamma → S.ρ gamma = -gamma := by
  classical
  obtain ⟨zeta, hzeta⟩ := CFSG.LieType.SeitzGeneration.exists_primitiveRoot_units
    (L := L) Nat.prime_two hp hp2
  have hzetaQ : zeta ^ (S.D.q + 1) = 1 := by
    obtain ⟨m, hm⟩ := hplus
    rw [hm, pow_mul, hzeta.pow_eq_one, one_pow]
  have hzetaInv : zeta ^ S.D.q = zeta⁻¹ := by
    apply eq_inv_iff_mul_eq_one.mpr
    rw [← pow_succ]
    exact hzetaQ
  have hcox : coxeterMatrix (isFiniteType_cartan .E7) = CoxeterMatrix.E₇ :=
    CFSG.ClassicalInvolution.Phan.PhanE.coxeterMatrix_cartanE7
      (isFiniteType_cartan .E7) cartan_E7
  have hconn : GGSimplyLacedConnected (coxeterMatrix (isFiniteType_cartan .E7)) := by
    rw [hcox]
    change GGSimplyLacedConnected (CoxeterMatrix.E₇ : CoxeterMatrix (Fin 7))
    apply ggSimplyLacedConnected_of_weyl
    · exact Or.inr (Or.inr (Or.inl ⟨Equiv.refl (Fin 7), by rfl⟩))
    · exact (show GGIsWeylMatrixE CoxeterMatrix.E₇ from
        Or.inr (Or.inl ⟨Equiv.refl (Fin 7), by rfl⟩)).le_three
  intro gamma hgamma
  have hcoords : ∀ j, (p : ℤ) ∣ (S.ρ gamma) j + gamma j := by
    intro j
    let a : Fin (Tag.rank .E7) → Lˣ := fun k => if k = j then zeta else 1
    have hap : ∀ k, a k ^ p = 1 := by
      intro k
      by_cases hkj : k = j <;> simp [a, hkj, hzeta.pow_eq_one]
    have heval : ∀ delta : Fin (Tag.rank .E7) → ℤ,
        rootChar a delta = zeta ^ delta j := by
      intro delta
      unfold rootChar
      rw [Finset.prod_eq_single j]
      · simp [a]
      · intro k _ hkj
        simp [a, hkj]
      · simp
    have hchar := S.frob.rootChar_eq a (hfull a hap) gamma hgamma
    rw [heval, heval] at hchar
    have hcomm : (zeta ^ gamma j) ^ S.D.q = (zeta ^ S.D.q) ^ gamma j := by
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]
    have hpow : zeta ^ (S.ρ gamma) j = zeta ^ (-gamma j) := by
      rw [hchar, hcomm, hzetaInv]
      simp [zpow_neg]
    apply (hzeta.zpow_eq_one_iff_dvd ((S.ρ gamma) j + gamma j)).mp
    rw [zpow_add, hpow, zpow_neg, inv_mul_cancel]
  apply ggRootKer_eq_of_rad (isFiniteType_cartan .E7) posDef_cartan_E7 hconn
    (by norm_num [Tag.rank]) hp hp2
    (isRoot_iff_mem_roots.mp (isRoot_neg_iff.mpr hgamma))
    (isRoot_iff_mem_roots.mp ((S.frob.isRoot_iff gamma).mpr hgamma))
  intro l
  change (p : ℤ) ∣ ∑ k, (Tag.cartan .E7) l k * ((S.ρ gamma) k - (-gamma) k)
  apply Finset.dvd_sum
  intro k _
  exact dvd_mul_of_dvd_right (by simpa using hcoords k) _

variable {G : Type} [Group G] [Finite G]

private theorem exists_langData_of_toral_original_E7_bstar_actor
    (hTB : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    {ι : Type} {N : CoxeterMatrix ι} {e : N.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) N e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, N = CoxeterMatrix.E₇.reindex σ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hrange : lambda.range = ggG0 p B x L D J)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (Γ : Bs →* MulAut (e7Data_valid.minGroup K))
    (hΓ : ∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹)
    (y : e7Data_valid.minGroup K)
    (hinner : Γ ⟨x, hcfg.1.1.tableB_facts.2.2.1⟩ = MulAut.conj y)
    (htoral : ∃ g ∈ adjointGroup .E7 (AlgebraicClosure K),
      ∀ u : e7Data_valid.minGroup K, lambda u ∈ Bs →
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (e7MinEquivAdjoint K u : ModGL .E7 K) * g ∈ torusGroup .E7 (AlgebraicClosure K)) :
    lambda y = x ∧
      ∃ (S : LangSetup .E7 (AlgebraicClosure K) 5)
        (a : Fin (Tag.rank .E7) → (AlgebraicClosure K)ˣ)
        (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K)),
        S.D.q = Nat.card K ∧
        (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
          (∀ c, Fr c = c ^ Nat.card K) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
        (∀ c, iota c = S.D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL .E7 K) * S.D.g0) ∧
        Function.Injective iota ∧ iota.range = S.Γ ∧
        (∀ u : e7Data_valid.minGroup K, lambda u ∈ Bs →
          iota (e7MinEquivAdjoint K u) ∈ S.D.torus) ∧
        (∀ z : ModGL .E7 (AlgebraicClosure K),
          (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
            iota (e7MinEquivAdjoint K u) = z) ↔
          ∃ b : Fin (Tag.rank .E7) → (AlgebraicClosure K)ˣ,
            (∀ i, b i ^ p = 1) ∧ rootDiagUnit .E7 b = z) ∧
        rootDiagUnit .E7 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧
        rootDiagUnit .E7 a ≠ 1 ∧ iota (e7MinEquivAdjoint K y) = rootDiagUnit .E7 a := by
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have : Fact p.Prime := ⟨hp⟩
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ := center_minGroup_e7_eq_bot
  have hlambda : Function.Injective lambda :=
    (MonoidHom.ker_eq_bot_iff lambda).mp (le_antisymm (by simpa only [hZ] using hker) bot_le)
  have : Finite (e7Data_valid.minGroup K) := Finite.of_injective lambda hlambda
  have hy := hcfg.lambda_native_actor_eq_of_original_E7 hTB hWI hpres hE7 hJoin
    K lambda hrange hker Γ hΓ y hinner
  have hBs : IsElemAbelian p Bs := hcfg.1.1.tableB_facts.2.1
  let theta := e7MinEquivAdjoint K
  let E := Bs.comap lambda
  let E0 := E.map theta.toMonoidHom
  have hE : IsElemAbelian p E := CFSG.Open.IsElemAbelian.comap hBs hlambda
  have hE0 : IsElemAbelian p E0 := CFSG.Open.IsElemAbelian.map hE theta.toMonoidHom
  obtain ⟨g, hg, htor⟩ := htoral
  have htorE0 : ∃ g ∈ adjointGroup .E7 (AlgebraicClosure K), ∀ u ∈ E0,
      g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (u : ModGL .E7 K) * g ∈
        torusGroup .E7 (AlgebraicClosure K) := by
    refine ⟨g, hg, ?_⟩
    rintro u ⟨v, hv, rfl⟩
    exact htor v hv
  have hnotp : ¬ p ∣ Nat.card K := by
    let : Fintype K := Fintype.ofFinite K
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    rw [Nat.card_eq_fintype_card, hf]
    intro h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
  obtain ⟨w, Fr, hFr, g0, hg0, hg0Fr, hEin⟩ :=
    ExcFramesHalf.exists_langTorus_of_toral hp K hnotp E0 hE0 htorE0
  have hOne : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
      ((1 : adjointGroup .E7 K) : ModGL .E7 K) * g0 ∈
      (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0 hg0Fr).torus := by
    simpa only [Subgroup.coe_one, map_one, mul_one, inv_mul_cancel] using
      (LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0 hg0Fr).torus.one_mem
  obtain ⟨S, _a0, iota, hSD, _h0T, _h0p, hiota, hiotaRange, hiotaEq, _h0act⟩ :=
    exists_langSetup_conj_of_prime_bound (Or.inr (Or.inr (Or.inl rfl))) K
      Nat.prime_five (by decide) (Or.inl le_rfl) hFr hg0 hg0Fr 1 (by simp) hOne
  have hwhole : ∀ u : e7Data_valid.minGroup K, lambda u ∈ Bs →
      iota (theta u) ∈ S.D.torus := by
    intro u hu
    obtain ⟨z, hz, hzEq⟩ := Subgroup.mem_map.mp
      (hEin (theta u) (Subgroup.mem_map_of_mem theta.toMonoidHom hu))
    change g0 * z * g0⁻¹ = baseChangeGL (algebraMap K (AlgebraicClosure K))
      (theta u : ModGL .E7 K) at hzEq
    have hback : g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (theta u : ModGL .E7 K) * g0 = z := by
      rw [← hzEq]
      group
    rw [hiotaEq, hSD]
    exact hback.symm ▸ hz
  let phi := iota.comp theta.toMonoidHom
  let A := E.map phi
  have hphi : Function.Injective phi := hiota.comp theta.injective
  have hA : IsElemAbelian p A := CFSG.Open.IsElemAbelian.map hE phi
  let Omega := AlgebraicClosure K
  let mu := rootsOfUnity p Omega
  let lift : (Fin (Tag.rank .E7) → mu) →* (Fin (Tag.rank .E7) → Omegaˣ) :=
    { toFun := fun b i => (b i : Omegaˣ)
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  let torsionHom := (rootDiagUnitHom .E7 Omega).comp lift
  let T := torsionHom.range
  have hlift : Function.Injective lift := by
    intro b c h
    funext i
    exact Subtype.ext (congrFun h i)
  have htorsion : Function.Injective torsionHom := rootDiagUnit_injective.comp hlift
  have : Finite T := Finite.of_equiv (Fin (Tag.rank .E7) → mu)
    (MonoidHom.ofInjective htorsion).toEquiv
  have hTcard : Nat.card T ≤ p ^ 7 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective htorsion).toEquiv,
      Nat.card_fun, Nat.card_fin]
    simpa only [Tag.rank] using Nat.pow_le_pow_left (card_rootsOfUnity Omega p : Nat.card mu ≤ p) 7
  have hAT : A ≤ T := by
    intro z hz
    have hzT : z ∈ S.D.torus := by
      obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hz
      exact hwhole u hu
    rw [hSD] at hzT
    obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup
      (CFSG.RankThree.PartOne.KE.mem_twistedTorusOf.mp hzT).1
    have hbp : b ^ p = 1 := by
      apply rootDiagUnit_injective
      have hp : rootDiagUnit .E7 (b ^ p) = rootDiagUnit .E7 b ^ p :=
        (rootDiagUnitHom .E7 Omega).map_pow b p
      rw [hp, ← hb, hA.2 z hz, rootDiagUnit_one]
    refine MonoidHom.mem_range.mpr ⟨fun i => ⟨b i, ?_⟩, hb.symm⟩
    change b i ^ p = 1
    exact congrFun hbp i
  have hBsRange : Bs ≤ lambda.range := by
    rw [hrange]
    exact bstar_le_ggG0_of_original_E7 hTB hWI hcfg hpres hE7 hJoin
  have hEmap : E.map lambda = Bs := Subgroup.map_comap_eq_self hBsRange
  have hEcard : Nat.card E = Nat.card Bs := by
    rw [← hEmap, Subgroup.card_map_of_injective hlambda]
  have hAcard : Nat.card A = Nat.card Bs := by
    rw [Subgroup.card_map_of_injective hphi, hEcard]
  have hW : GGWeylOfType p CoxeterMatrix.E₇ (ggAutomizerJoin L Bs 𝒦) := by
    obtain ⟨sigma, rfl⟩ := hE7
    exact GGWeylOfType.of_reindex ⟨e, hpres.2⟩
  have hlow : p ^ 7 ≤ Nat.card Bs := FrameRoute.pow_le_card_of_weylOfType_of_two
    hp hp2 hBs hW FrameRoute.exists_elemAbelian_two_coxeterE7
  have hEq : A = T := Subgroup.eq_of_le_of_card_ge hAT (by rw [hAcard]; exact hTcard.trans hlow)
  have hTmem : ∀ z : ModGL .E7 Omega, z ∈ T ↔
      ∃ b : Fin (Tag.rank .E7) → Omegaˣ, (∀ i, b i ^ p = 1) ∧ rootDiagUnit .E7 b = z := by
    intro z
    constructor
    · rintro ⟨b, rfl⟩
      refine ⟨fun i => (b i : Omegaˣ), ?_, rfl⟩
      intro i
      exact (b i).2
    · rintro ⟨b, hbp, hb⟩
      exact ⟨fun i => ⟨b i, hbp i⟩, hb⟩
  have hfull : ∀ z : ModGL .E7 Omega,
      (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧ iota (theta u) = z) ↔
      ∃ b : Fin (Tag.rank .E7) → Omegaˣ, (∀ i, b i ^ p = 1) ∧ rootDiagUnit .E7 b = z := by
    intro z
    change (∃ u, u ∈ E ∧ phi u = z) ↔ _
    rw [← Subgroup.mem_map]
    change z ∈ A ↔ _
    rw [hEq]
    exact hTmem z
  obtain ⟨a, hap, ha⟩ := (hfull (iota (theta y))).mp
    ⟨y, hy.symm ▸ hcfg.1.1.tableB_facts.2.2.1, rfl⟩
  have hne : rootDiagUnit .E7 a ≠ 1 := by
    intro h
    have hy1 : y = 1 := by
      apply hphi
      change iota (theta y) = iota (theta 1)
      rw [← ha, h, map_one, map_one]
    have hx1 : x = 1 := by rw [← hy, hy1, map_one]
    have horder := hcfg.1.1.orderOf_x
    rw [hx1, orderOf_one] at horder
    exact hp.ne_one horder.symm
  refine ⟨hy, S, a, iota, ?_, ⟨Fr, hFr, ?_⟩, ?_, hiota, hiotaRange,
    hwhole, hfull, ?_, hap, hne, ha.symm⟩
  · rw [hSD]
    rfl
  · rw [hSD]
    rfl
  · intro c
    rw [hiotaEq, hSD]
    rfl
  · rw [ha]
    exact hwhole y (hy.symm ▸ hcfg.1.1.tableB_facts.2.2.1)

theorem exists_langData_of_original_E7_bstar_actor
    (hTB : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {ι : Type} {N : CoxeterMatrix ι} {e : N.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres 3 (ggAutomizerJoin L Bs 𝒦) N e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, N = CoxeterMatrix.E₇.reindex σ)
    (hJoin : ggG0 3 B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hrange : lambda.range = ggG0 3 B x L D J)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (Γ : Bs →* MulAut (e7Data_valid.minGroup K))
    (hΓ : ∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹)
    (y : e7Data_valid.minGroup K)
    (hinner : Γ ⟨x, hcfg.1.1.tableB_facts.2.2.1⟩ = MulAut.conj y) :
    lambda y = x ∧
      ∃ (S : LangSetup .E7 (AlgebraicClosure K) 5)
        (a : Fin (Tag.rank .E7) → (AlgebraicClosure K)ˣ)
        (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K)),
        S.D.q = Nat.card K ∧
        (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
          (∀ c, Fr c = c ^ Nat.card K) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
        (∀ c, iota c = S.D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL .E7 K) * S.D.g0) ∧
        Function.Injective iota ∧ iota.range = S.Γ ∧
        (∀ u : e7Data_valid.minGroup K, lambda u ∈ Bs →
          iota (e7MinEquivAdjoint K u) ∈ S.D.torus) ∧
        (∀ z : ModGL .E7 (AlgebraicClosure K),
          (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
            iota (e7MinEquivAdjoint K u) = z) ↔
          ∃ b : Fin (Tag.rank .E7) → (AlgebraicClosure K)ˣ,
            (∀ i, b i ^ 3 = 1) ∧ rootDiagUnit .E7 b = z) ∧
        rootDiagUnit .E7 a ∈ S.D.torus ∧ (∀ i, a i ^ 3 = 1) ∧
        rootDiagUnit .E7 a ≠ 1 ∧ iota (e7MinEquivAdjoint K y) = rootDiagUnit .E7 a := by
  exact exists_langData_of_toral_original_E7_bstar_actor hTB hWI hcfg hpres hE7 hJoin
    K lambda hrange hker Γ hΓ y hinner
    (exists_conj_torus_of_original_E7_bstar hTB hWI hcfg hpres hE7 hJoin
      K lambda hrange hker)

theorem exists_langData_of_original_E7_bstar_actor_of_ne_three
    (hTB : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦) (hp3 : p ≠ 3)
    {ι : Type} {N : CoxeterMatrix ι} {e : N.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) N e)
    (hE7 : ∃ σ : Fin 7 ≃ ι, N = CoxeterMatrix.E₇.reindex σ)
    (hJoin : ggG0 p B x L D J = L ⊔ ⨆ K ∈ 𝒦, K)
    (K : Type) [Field K] [Finite K] [CharP K 2]
    (lambda : e7Data_valid.minGroup K →* G)
    (hrange : lambda.range = ggG0 p B x L D J)
    (hker : lambda.ker ≤ Subgroup.center (e7Data_valid.minGroup K))
    (Γ : Bs →* MulAut (e7Data_valid.minGroup K))
    (hΓ : ∀ b z, lambda (Γ b z) = (b : G) * lambda z * (b : G)⁻¹)
    (y : e7Data_valid.minGroup K)
    (hinner : Γ ⟨x, hcfg.1.1.tableB_facts.2.2.1⟩ = MulAut.conj y) :
    lambda y = x ∧
      ∃ (S : LangSetup .E7 (AlgebraicClosure K) 5)
        (a : Fin (Tag.rank .E7) → (AlgebraicClosure K)ˣ)
        (iota : adjointGroup .E7 K →* ModGL .E7 (AlgebraicClosure K)),
        S.D.q = Nat.card K ∧
        (∃ Fr : AlgebraicClosure K →+* AlgebraicClosure K,
          (∀ c, Fr c = c ^ Nat.card K) ∧ S.D.Φ = Units.map (entrywiseHom Fr)) ∧
        (∀ c, iota c = S.D.g0⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (c : ModGL .E7 K) * S.D.g0) ∧
        Function.Injective iota ∧ iota.range = S.Γ ∧
        (∀ u : e7Data_valid.minGroup K, lambda u ∈ Bs →
          iota (e7MinEquivAdjoint K u) ∈ S.D.torus) ∧
        (∀ z : ModGL .E7 (AlgebraicClosure K),
          (∃ u : e7Data_valid.minGroup K, lambda u ∈ Bs ∧
            iota (e7MinEquivAdjoint K u) = z) ↔
          ∃ b : Fin (Tag.rank .E7) → (AlgebraicClosure K)ˣ,
            (∀ i, b i ^ p = 1) ∧ rootDiagUnit .E7 b = z) ∧
        rootDiagUnit .E7 a ∈ S.D.torus ∧ (∀ i, a i ^ p = 1) ∧
        rootDiagUnit .E7 a ≠ 1 ∧ iota (e7MinEquivAdjoint K y) = rootDiagUnit .E7 a := by
  classical
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hcfg
  have hZ : Subgroup.center (e7Data_valid.minGroup K) = ⊥ := center_minGroup_e7_eq_bot
  have hinj : Function.Injective lambda :=
    (MonoidHom.ker_eq_bot_iff lambda).mp
      (le_antisymm (by simpa only [hZ] using hker) bot_le)
  have : Finite (e7Data_valid.minGroup K) := Finite.of_injective lambda hinj
  let theta := e7MinEquivAdjoint K
  let rho : e7Data_valid.minGroup K →* ModGL .E7 (AlgebraicClosure K) :=
    (baseChangeGL (algebraMap K (AlgebraicClosure K))).comp
      ((adjointGroup .E7 K).subtype.comp theta.toMonoidHom)
  let E := Bs.comap lambda
  let A := E.map rho
  have hrho : Function.Injective rho :=
    (baseChangeGL_injective _).comp (Subtype.val_injective.comp theta.injective)
  have hfinA : Finite A :=
    Finite.of_equiv E (Subgroup.equivMapOfInjective E rho hrho).toEquiv
  have hBs : IsElemAbelian p Bs := hcfg.1.1.tableB_facts.2.1
  have hE : IsElemAbelian p E := CFSG.Open.IsElemAbelian.comap hBs hinj
  have hA : IsElemAbelian p A := CFSG.Open.IsElemAbelian.map hE rho
  have hAadj : A ≤ adjointGroup .E7 (AlgebraicClosure K) := by
    rintro z ⟨u, -, rfl⟩
    exact TableBExcTwo.baseChangeGL_mem_adjointGroup _ (theta u).2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have halg : letI := ZMod.algebra (AlgebraicClosure K) 2;
      Algebra.IsAlgebraic (ZMod 2) (AlgebraicClosure K) :=
    CFSG.RankThree.PartOne.KE6.eqp_halg K (AlgebraicClosure K)
  have htorA := LieCore.isToralSubgroup_of_nonTorsion_of_ne_E8
    (τ := .E7) (by decide) hp hp2 (fun _ => hp3)
    (ℓ := 2) hp2.symm halg hAadj hfinA hA
  obtain ⟨g, hg, hgtor⟩ := htorA
  have htoral : ∃ g ∈ adjointGroup .E7 (AlgebraicClosure K),
      ∀ u : e7Data_valid.minGroup K, lambda u ∈ Bs →
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (e7MinEquivAdjoint K u : ModGL .E7 K) * g ∈ torusGroup .E7 (AlgebraicClosure K) := by
    refine ⟨g, hg, ?_⟩
    intro u hu
    exact hgtor (rho u) (Subgroup.mem_map_of_mem rho hu)
  exact exists_langData_of_toral_original_E7_bstar_actor hTB hWI hcfg hpres hE7 hJoin
    K lambda hrange hker Γ hΓ y hinner htoral

end CFSG.StandardType
