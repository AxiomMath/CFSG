module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P20o
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutSuzukiModel
import CFSG.LocalAnalysis.SectionRank.SuzukiCover
import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local
import CFSG.GroupActions.SelfCentralizingCoreOuterPrimeBound
import CFSG.Blueprint.Catalog
import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Walter.PSL2Facts.Even
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Cardinality
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2RootGroups
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

section Borel

open CFSG.BenderSuzuki.MatrixGroups CFSG.BenderSuzuki.PFAppendixIII
  CFSG.ComponentClassification.AschbacherToolkit.Bender.SuzukiAut CFSG.SectionRank

private theorem s208e_card_torusSub (m : ℕ) (hm : 0 < m) :
    Nat.card (torusSub m) = 2 ^ (2 * m + 1) - 1 := by
  let K := BinaryGaloisField (2 * m + 1)
  have hbij : Function.Bijective
      (fun x : Kˣ => (⟨torus m x, torus_mem m x⟩ : torusSub m)) := by
    refine ⟨fun x y hxy => szTorus_injective m (Subtype.ext_iff.mp hxy), fun g => ?_⟩
    obtain ⟨x, hx⟩ := (mem_torusSub m hm).mp g.2
    exact ⟨x, Subtype.ext hx.symm⟩
  calc Nat.card (torusSub m) = Nat.card Kˣ :=
        (Nat.card_congr (Equiv.ofBijective _ hbij)).symm
    _ = Nat.card K - 1 := Nat.card_units K
    _ = 2 ^ (2 * m + 1) - 1 := by rw [natCard_binaryGaloisField]

private theorem s208e_exists_torus_normalizing (m : ℕ) (hm : 0 < m)
    (S : Sylow 2 (SuzukiMatrixGroup m)) :
    ∃ D : Subgroup (SuzukiMatrixGroup m), Nat.card D = 2 ^ (2 * m + 1) - 1 ∧
      D ≤ Subgroup.normalizer ((S : Subgroup (SuzukiMatrixGroup m)) : Set _) := by
  obtain ⟨R, hR⟩ := exists_sylow_eq_rootSub m hm
  have : MulAction.IsPretransitive (SuzukiMatrixGroup m)
      (Sylow 2 (SuzukiMatrixGroup m)) := Sylow.isPretransitive_of_finite
  obtain ⟨g, hg⟩ := MulAction.IsPretransitive.exists_smul_eq
    (M := SuzukiMatrixGroup m) R S
  have hS : (S : Subgroup (SuzukiMatrixGroup m)) =
      (rootSub m).map (MulAut.conj g).toMonoidHom := by
    rw [← congrArg (fun P : Sylow 2 (SuzukiMatrixGroup m) =>
      (P : Subgroup (SuzukiMatrixGroup m))) hg, Sylow.coe_subgroup_smul, hR,
      CFSG.GroupActions.mulAut_smul_subgroup_eq_map]
  refine ⟨(torusSub m).map (MulAut.conj g).toMonoidHom, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact s208e_card_torusSub m hm
  · have hTH : (torusSub m).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer
          (((rootSub m).map (MulAut.conj g).toMonoidHom :
            Subgroup (SuzukiMatrixGroup m)) : Set (SuzukiMatrixGroup m)) := by
      rw [← Subgroup.map_equiv_normalizer_eq]
      exact Subgroup.map_mono (torusSub_le_normalizer m)
    rwa [← hS] at hTH

private theorem s208e_sz_borel {X : Type} [Group X] [Finite X] {a : ℕ} (hSz : IsSz X a)
    (S : Sylow 2 X) : ∃ D : Subgroup X, Nat.card D = 2 ^ a - 1 ∧
      D ≤ Subgroup.normalizer ((S : Subgroup X) : Set X) := by
  obtain ⟨m, hm, rfl, ⟨e⟩⟩ :=
    CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_sz_of_lieModel_twistedB2 hSz
  let e' : X ≃* SuzukiMatrixGroup m :=
    e.trans (CFSG.SignalizerFunctorTheorem.McBride.SzModel.szEquiv m)
  let S' : Sylow 2 (SuzukiMatrixGroup m) :=
    Sylow.mapSurjective (f := e'.toMonoidHom) e'.surjective S
  have hS' : (S' : Subgroup (SuzukiMatrixGroup m)) =
      (S : Subgroup X).map e'.toMonoidHom := rfl
  obtain ⟨D, hDcard, hDnorm⟩ := s208e_exists_torus_normalizing m hm S'
  refine ⟨D.comap e'.toMonoidHom, ?_, ?_⟩
  · have hcard : Nat.card (D.comap e'.toMonoidHom) = Nat.card D := by
      rw [Subgroup.comap_equiv_eq_map_symm',
        Subgroup.card_map_of_injective e'.symm.injective]
    rw [hcard, hDcard]
  · intro x hx
    rw [Subgroup.mem_comap] at hx
    have hx' : e' x ∈ Subgroup.normalizer
        ((S' : Subgroup (SuzukiMatrixGroup m)) : Set _) := hDnorm hx
    have hle : x ∈ Subgroup.normalizer
        (((S' : Subgroup (SuzukiMatrixGroup m))).comap e'.toMonoidHom : Set X) :=
      Subgroup.le_normalizer_comap e'.toMonoidHom hx'
    have hScomap : ((S' : Subgroup (SuzukiMatrixGroup m)).comap e'.toMonoidHom :
        Subgroup X) = (S : Subgroup X) := by
      rw [hS', Subgroup.comap_map_eq_self_of_injective e'.injective]
    rwa [hScomap] at hle

end Borel

private theorem s208e_isL2_psl {X : Type} [Group X] {n : ℕ} (h : IsL2 X n) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧ CharP F 2 ∧
      Nonempty (X ≃* CFSG.GorensteinWalter.PSL2 F) := by
  obtain ⟨-, F, hF1, hF2, hFcard, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel h (by decide)
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := n) (by rw [← Nat.card_eq_fintype_card, hFcard])
  exact ⟨F, hF1, hF2, hFcard, inferInstance,
    ⟨e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 F).symm⟩⟩

private theorem s208e_L2_card {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  obtain ⟨F, _, _, hFcard, _, ⟨e⟩⟩ := s208e_isL2_psl h
  rw [Nat.card_congr (e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo).toEquiv,
    CFSG.GorensteinWalter.sl2_card_formula, hFcard]

private theorem s208e_L2_card_normalizer {X : Type} [Group X] [Finite X] {n : ℕ} (h : IsL2 X n)
    (U : Sylow 2 X) : Nat.card (normalizer ((U : Subgroup X) : Set X)) * (2 ^ n + 1) =
      Nat.card X := by
  obtain ⟨F, _, _, hFcard, _, ⟨e⟩⟩ := s208e_isL2_psl h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U' : Sylow 2 (CFSG.GorensteinWalter.PSL2 F) :=
    Sylow.mapSurjective (f := e.toMonoidHom) e.surjective U
  have hN : (normalizer ((U : Subgroup X) : Set X)).map e.toMonoidHom =
      normalizer ((U' : Subgroup (CFSG.GorensteinWalter.PSL2 F)) :
        Set (CFSG.GorensteinWalter.PSL2 F)) := by
    rw [Subgroup.map_equiv_normalizer_eq]
    rfl
  have hcard1 : Nat.card (normalizer ((U : Subgroup X) : Set X)) =
      Nat.card (normalizer ((U' : Subgroup (CFSG.GorensteinWalter.PSL2 F)) :
        Set (CFSG.GorensteinWalter.PSL2 F))) := by
    rw [← hN, Subgroup.card_map_of_injective e.injective]
  have hsyl : Nat.card (Sylow 2 (CFSG.GorensteinWalter.PSL2 F)) = 2 ^ n + 1 := by
    rw [← Nat.card_congr (CFSG.GorensteinWalter.psl2ProjectiveLineEquivSylow F hFcard),
      CFSG.GorensteinWalter.PSL2ProjectiveLine,
      Projectivization.card_of_finrank_two _ _ (by simp), hFcard]
  have h3 : (normalizer ((U' : Subgroup (CFSG.GorensteinWalter.PSL2 F)) :
      Set (CFSG.GorensteinWalter.PSL2 F))).index = 2 ^ n + 1 := by
    rw [← hsyl, U'.card_eq_index_normalizer]
    rfl
  rw [hcard1, ← h3, mul_comm, Subgroup.index_mul_card, Nat.card_congr e.toEquiv]

private theorem s208e_center_bot {X : Type} [Group X] {n : ℕ} (h : IsSz X n ∨ IsL2 X n) :
    center X = ⊥ := by
  rcases h with h | h
  · have : IsSimpleGroup X := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 h
    obtain ⟨a, b, hab⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mul_ne_of_lieModel_twistedB2 h
    rcases (center X).normal_of_characteristic.eq_bot_or_eq_top with hZ | hZ
    · exact hZ
    · exact absurd ((Subgroup.mem_center_iff.1 (hZ ▸ Subgroup.mem_top a) b).symm) hab
  · obtain ⟨F, _, _, _, _, ⟨e⟩⟩ := s208e_isL2_psl h
    let e' : X ≃* Matrix.SpecialLinearGroup (Fin 2) F :=
      e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have h1 : e' x ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨y, rfl⟩ := e'.surjective g
      rw [← map_mul, ← map_mul]
      exact congrArg e' (Subgroup.mem_center_iff.1 hx y)
    rw [CFSG.Walter.sl2_center_eq_bot_of_charTwo, Subgroup.mem_bot] at h1
    exact e'.injective (h1.trans (map_one e').symm)

private theorem s208e_ne_two {n p : ℕ} (hpn : p ∣ 2 ^ n - 1) (hn : n ≠ 0) : p ≠ 2 := by
  rintro rfl
  have h1 : 2 ∣ 2 ^ n := dvd_pow_self 2 hn
  have h3 : 2 ∣ 2 ^ n - (2 ^ n - 1) := Nat.dvd_sub h1 hpn
  rw [Nat.sub_sub_self Nat.one_le_two_pow] at h3
  exact absurd h3 (by norm_num)

private theorem s208e_pRank_bar {G : Type} [Group G] [Finite G] (X : Subgroup G) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    CFSG.Open.pRank p (⊤ : Subgroup (Bar2 X)) = CFSG.Open.pRank p X := by
  have : Fact p.Prime := ⟨hp⟩
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup X]
  exact CFSG.SectionRank.pRank_quotient_eq (p := p) (G := ↥X) (CFSG.pCore 2 ↥X)
    (uc22p20c_not_dvd_card_of_isPGroup_two CFSG.pCore_isPGroup hp hp2)

private theorem s208e_isElemAbelian_zpowers {Y : Type} [Group Y] {p : ℕ} {x : Y}
    (hx : x ^ p = 1) : IsElemAbelian p (zpowers x) := by
  refine ⟨inferInstance, fun y hy => ?_⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx, one_zpow]

private theorem s208e_sup_zpowers {Y : Type} [Group Y] [Finite Y] {p : ℕ} (hp : p.Prime)
    {A W : Subgroup Y} {z : Y} (hzA : z ∈ A) (hzp : z ^ p = 1) (hz : ∃ a ∈ A, a * z ≠ z * a)
    (hW : W ≤ centralizer (A : Set Y)) (hWe : IsElemAbelian p W) {k : ℕ}
    (hWc : Nat.card W = p ^ k) :
    IsElemAbelian p (W ⊔ zpowers z) ∧ Nat.card (W ⊔ zpowers z : Subgroup Y) = p ^ (k + 1) := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨a, ha, hne⟩ := hz
  have hz1 : z ≠ 1 := fun h => hne (by rw [h, mul_one, one_mul])
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1
  have hzle : zpowers z ≤ A := (Subgroup.zpowers_le).2 hzA
  refine uc22p20p_sup_elemAbelian
    (fun w hw y hy => (Subgroup.mem_centralizer_iff.1 (hW hw) y (hzle hy)).symm) le_rfl le_rfl hWe
    (s208e_isElemAbelian_zpowers hzp) hWc (by rw [Nat.card_zpowers, hzo, pow_one]) ?_
  rintro x ⟨hxW, hxz⟩ -
  by_contra hx1
  have hdvd : orderOf x ∣ p := hzo ▸ orderOf_dvd_of_mem_zpowers hxz
  rcases (Nat.dvd_prime hp).1 hdvd with h1 | h1
  · exact hx1 (orderOf_eq_one_iff.1 h1)
  · have heq : zpowers x = zpowers z := Subgroup.eq_of_le_of_card_ge
      ((Subgroup.zpowers_le).2 hxz) (by rw [Nat.card_zpowers, Nat.card_zpowers, h1, hzo])
    have hzW : z ∈ W := (Subgroup.zpowers_le).2 hxW (heq ▸ Subgroup.mem_zpowers z)
    exact hne (Subgroup.mem_centralizer_iff.1 (hW hzW) a ha)

variable {G : Type} [Group G] [Finite G]

theorem s208e_borel_prop {X : Type} [Group X] [Finite X] {n : ℕ} (_hn : 2 < n)
    (h : IsSz X n ∨ IsL2 X n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    ∀ P : Sylow 2 X, ∃ x ∈ normalizer ((P : Subgroup X) : Set X), orderOf x = p ∧
      x ∉ center X := by
  have : Fact p.Prime := ⟨hp⟩
  have hZ := s208e_center_bot h
  have hnc : ∀ x : X, orderOf x = p → x ∉ center X := fun x hx hxZ => by
    rw [hZ, Subgroup.mem_bot] at hxZ
    rw [hxZ, orderOf_one] at hx
    exact hp.one_lt.ne hx
  intro P
  obtain ⟨D, hD⟩ : ∃ D : Subgroup X, p ∣ Nat.card D ∧
      D ≤ normalizer ((P : Subgroup X) : Set X) := by
    rcases h with h | h
    · obtain ⟨D, hDc, hDn⟩ := s208e_sz_borel h P
      exact ⟨D, hDc ▸ hpn, hDn⟩
    · refine ⟨normalizer ((P : Subgroup X) : Set X), ?_, le_rfl⟩
      have h1 := s208e_L2_card_normalizer h P
      rw [s208e_L2_card h] at h1
      have h2 : (2 ^ n) ^ 2 - 1 = (2 ^ n + 1) * (2 ^ n - 1) := by
        rw [← Nat.sq_sub_sq, one_pow]
      have hN : Nat.card (normalizer ((P : Subgroup X) : Set X)) = 2 ^ n * (2 ^ n - 1) := by
        rw [h2] at h1
        have h3 : (2 ^ n + 1) * Nat.card (normalizer ((P : Subgroup X) : Set X)) =
            (2 ^ n + 1) * (2 ^ n * (2 ^ n - 1)) := by
          rw [mul_comm, h1]
          ring
        exact Nat.eq_of_mul_eq_mul_left (by positivity) h3
      rw [hN]
      exact hpn.mul_left _
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' p hD.1
  refine ⟨(y : X), hD.2 y.2, ?_, hnc _ ?_⟩ <;> rwa [Subgroup.orderOf_coe]

theorem s208e_oTwoE_orb_top {H K : Subgroup G} (hK : K ∈ CFSG.Quasithin.cComp H)
    (hq : CFSG.Open.IsQuasisimple (Bar2 K)) : OTwoE ↥(uc22p20bOrb H K) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L : Subgroup G := uc22p20bOrb H K
  have hcC : CFSG.Quasithin.cComp L = Set.range (fun t : H => uc22p20bCj (t : G) K) :=
    uc22p20b_cComp_orb hK le_rfl
  have hKt : ∀ t : H, uc22p20bCj (t : G) K ∈ CFSG.Quasithin.cComp L := fun t => by
    rw [hcC]; exact ⟨t, rfl⟩
  have hPn : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  have hPs : Group.IsSolvable ↥(CFSG.pCore 2 ↥L) := uc22p20d_pCore_solvable L
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) :=
    QuotientGroup.mk'_surjective _
  have hcomp : ∀ t : H, CFSG.IsComponent
      (((uc22p20bCj (t : G) K).subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) := by
    intro t
    have hKtL : uc22p20bCj (t : G) K ≤ L := CFSG.Quasithin.le_of_mem_cComp (hKt t)
    have hKtsub : CFSG.Open.IsSubnormal (uc22p20bCj (t : G) K) L :=
      CFSG.Quasithin.subnormal_of_mem_cComp (hKt t)
    have hK' : (uc22p20bCj (t : G) K).subgroupOf L ∈ CFSG.Quasithin.cComp (⊤ : Subgroup ↥L) :=
      CFSG.Quasithin.subgroupOf_mem_cComp (hKt t)
    have hKbar := CFSG.Quasithin.map_mem_cComp_top (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) hπ
      (by rw [QuotientGroup.ker_mk']; exact hPs) hK'
    refine ⟨?_, CFSG.Quasithin.A3.subnormal_top_iff.mp
      (CFSG.Quasithin.subnormal_of_mem_cComp hKbar)⟩
    obtain ⟨e, -⟩ := uc22p20d_bar2Equiv hKtL hKtsub
    obtain ⟨f⟩ := uc22p20d_bar2_conj (t : G) K
    have hqKt : CFSG.Open.IsQuasisimple (Bar2 (uc22p20bCj (t : G) K)) :=
      CFSG.Open.IsQuasisimple.of_mulEquiv f.symm hq
    exact CFSG.Quasithin.A3.isQuasisimple_iff_open.mpr
      (CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hqKt)
  have hlayer : CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L) = ⊤ := by
    have hW : L ≤ ((CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L)).comap
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L))).map L.subtype := by
      refine iSup_le fun t => ?_
      intro g hg
      have hgL : g ∈ L := CFSG.Quasithin.le_of_mem_cComp (hKt t) hg
      refine ⟨⟨g, hgL⟩, ?_, rfl⟩
      exact CFSG.LocalCores.component_le_layer (hcomp t)
        ⟨⟨g, hgL⟩, Subgroup.mem_subgroupOf.2 hg, rfl⟩
    rw [eq_top_iff]
    intro y _
    obtain ⟨x, rfl⟩ := hπ y
    obtain ⟨x', hx', hxx'⟩ := hW x.2
    have : x' = x := Subtype.ext hxx'
    exact this ▸ hx'
  show (CFSG.layer (↥L ⧸ CFSG.pCore 2 ↥L)).comap (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤
  rw [hlayer]
  exact Subgroup.comap_top _

theorem s208e_rank_four (D : Data G) {H : Subgroup G} (hH : H ∈ hSet D.T D.M) {K : Subgroup G}
    (hK : K ∈ CFSG.Quasithin.cComp H) (hq : CFSG.Open.IsQuasisimple (Bar2 K)) (g : Fin 4 → G)
    (hg : ∀ i, g i ∈ H) (hinj : Function.Injective fun i => uc22p20bCj (g i) K) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2)
    (hP : ∀ P : Sylow 2 (Bar2 K), ∃ x ∈ normalizer ((P : Subgroup (Bar2 K)) : Set (Bar2 K)),
      orderOf x = p ∧ x ∉ center (Bar2 K)) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 4 ∧
      ∃ Z : Subgroup G, D.T ≤ Z ∧ Z ≤ H ∧ Group.IsSolvable ↥Z ∧ E ≤ Z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : OTwoE ↥(uc22p20bOrb H K) = ⊤ := s208e_oTwoE_orb_top hK hq
  set Y : Subgroup G := uc22p20bOrb H K
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp hK
  have hYH : Y ≤ H := uc22p20b_orb_le le_rfl hKH
  have hHn : H ≤ normalizer (Y : Set G) := uc22p20b_le_normalizer_orb H K
  have hspan : sSup (CFSG.Quasithin.cComp Y) = Y := uc22p20b_sSup_cComp_orb hK le_rfl
  have hcC : CFSG.Quasithin.cComp Y = Set.range (fun t : H => uc22p20bCj (t : G) K) :=
    uc22p20b_cComp_orb hK le_rfl
  have hKi : ∀ i, uc22p20bCj (g i) K ∈ CFSG.Quasithin.cComp Y := fun i => by
    rw [hcC]; exact ⟨⟨g i, hg i⟩, rfl⟩
  have hKiY : ∀ i, uc22p20bCj (g i) K ≤ Y := fun i => CFSG.Quasithin.le_of_mem_cComp (hKi i)
  have hKisub : ∀ i, CFSG.Open.IsSubnormal (uc22p20bCj (g i) K) Y := fun i =>
    CFSG.Quasithin.subnormal_of_mem_cComp (hKi i)
  have hne : ∀ i j, i ≠ j → uc22p20bCj (g i) K ≠ uc22p20bCj (g j) K :=
    fun i j h h' => h (hinj h')
  have e : ∀ i, Bar2 K ≃* Bar2 (uc22p20bCj (g i) K) := fun i =>
    (uc22p20d_bar2_conj (g i) K).some
  have hPn : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  let φ : ↥Y →* ↥Y ⧸ CFSG.pCore 2 ↥Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  let A : Fin 4 → Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := fun i =>
    ((uc22p20bCj (g i) K).subgroupOf Y).map φ
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := fun i j hij =>
    uc22p20d_commute_images hO (hKi i) (hKi j) (hne i j hij)
  have hmemA : ∀ (i : Fin 4) (c : ↥(uc22p20bCj (g i) K)),
      (QuotientGroup.mk (Subgroup.inclusion (hKiY i) c) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ A i :=
    fun i c => Subgroup.mem_map.2 ⟨Subgroup.inclusion (hKiY i) c,
      Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  set U : Subgroup G := D.T ⊓ Y with hU
  have hTH : CFSG.ABGLocalTools.IsSylowOf 2 D.T H := D.sylowG.of_le hH.1 le_top
  have hUY : CFSG.ABGLocalTools.IsSylowOf 2 U Y := hTH.inf_of_le_normalizer hYH hHn
  have hSyl := uc22p20d_isSylowOf_inf_comp hspan hUY
  have hsel : ∀ i, ∃ c : ↥(uc22p20bCj (g i) K),
      ((c : ↥(uc22p20bCj (g i) K)) : G) ∈ uc22p20dB U (uc22p20bCj (g i) K) ∧
        orderOf (QuotientGroup.mk c : Bar2 (uc22p20bCj (g i) K)) = p ∧
        (QuotientGroup.mk c : Bar2 (uc22p20bCj (g i) K)) ∉
          Subgroup.center (Bar2 (uc22p20bCj (g i) K)) := fun i =>
    uc22p20d_mem_B (hSyl _ (hKi i)) p (uc22p20d_transport_sylow (e i) hP)
  choose c hcB hco hcz using hsel
  have hprops := fun i => uc22p20d_image_props (hKiY i) (hKisub i) (p := p) (c i)
    (by rw [← hco i]; exact pow_orderOf_eq_one _) (hcz i)
  obtain ⟨E₀, hE₀le, hE₀, hE₀c⟩ := uc22p20d_elemAbelian_of_commuting
    (X := ↥Y ⧸ CFSG.pCore 2 ↥Y) p 4 hp A
    (fun i => (QuotientGroup.mk (Subgroup.inclusion (hKiY i) (c i)) : ↥Y ⧸ CFSG.pCore 2 ↥Y))
    hcomm (fun i => hmemA i (c i)) (fun i => (hprops i).1) (fun i => (hprops i).2)
  set D' : Subgroup G := uc22p20dD U (CFSG.Quasithin.cComp Y)
  have hD'mem : ∀ i, ((c i : ↥(uc22p20bCj (g i) K)) : G) ∈ D' := fun i =>
    (le_iSup₂ (f := fun (C : Subgroup G) (_ : C ∈ CFSG.Quasithin.cComp Y) => uc22p20dB U C)
      (uc22p20bCj (g i) K) (hKi i)) (hcB i)
  have hD'Y : D' ≤ Y := iSup₂_le fun C hC =>
    (uc22p20dB_le U C).trans (CFSG.Quasithin.le_of_mem_cComp hC)
  obtain ⟨E, hEB, hE, hEc⟩ := uc22p20d_lift_elemAbelian (CFSG.pCore 2 ↥Y)
    (CFSG.pCore_isPGroup) hp hp2 (D'.subgroupOf Y) E₀ hE₀ hE₀c (by
      refine hE₀le.trans ((Subgroup.closure_le _).2 ?_)
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_map.2 ⟨Subgroup.inclusion (hKiY i) (c i),
        Subgroup.mem_subgroupOf.2 (hD'mem i), rfl⟩)
  have hEG : E.map Y.subtype ≤ D' := by
    rintro _ ⟨x, hx, rfl⟩
    exact Subgroup.mem_subgroupOf.1 (hEB hx)
  have hDsolv : Group.IsSolvable ↥D' := uc22p20d_solvable_D hO hspan hUY
  have hTY : D.T ≤ normalizer (Y : Set G) := hH.1.trans hHn
  have h𝒪 : ∀ t ∈ D.T, ∀ C ∈ CFSG.Quasithin.cComp Y,
      uc22p20bCj t C ∈ CFSG.Quasithin.cComp Y := by
    intro t ht C hC
    rw [hcC] at hC ⊢
    obtain ⟨⟨s, hs⟩, rfl⟩ := hC
    exact ⟨⟨t * s, H.mul_mem (hH.1 ht) hs⟩, (uc22p20b_cj_cj t s K).symm⟩
  have hTn : D.T ≤ normalizer (D' : Set G) :=
    uc22p20d_T_le_normalizer_D hU hTY (CFSG.Quasithin.cComp Y) h𝒪
  have hTs : Group.IsSolvable ↥D.T := by
    have : Group.IsNilpotent ↥D.T := D.sylowM.isPGroup.isNilpotent
    infer_instance
  have hZs : Group.IsSolvable ↥(D' ⊔ D.T) :=
    CFSG.Quasithin.A3.isSolvable_sup_of_le_normalizer hTn
  refine ⟨E.map Y.subtype, (hEG.trans hD'Y).trans hYH,
    uc22p20d_isElemAbelian_map Y.subtype Y.subtype_injective hE, ?_,
    D' ⊔ D.T, le_sup_right, sup_le (hD'Y.trans hYH) hH.1, hZs, hEG.trans le_sup_left⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hEc]

theorem s208e_rank_SU3 (hU38 : uc22p20oU38Witness) {H K : Subgroup G}
    (hK : K ∈ CFSG.Quasithin.cComp H) (hU : IsSU3 (Bar2 K) 3) (g : Fin 3 → G)
    (hg : ∀ i, g i ∈ H) (hinj : Function.Injective fun i => uc22p20bCj (g i) K) :
    ∃ E : Subgroup G, E ≤ H ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO : OTwoE ↥(uc22p20bOrb H K) = ⊤ := s208e_oTwoE_orb_top hK hU.1
  set Y : Subgroup G := uc22p20bOrb H K
  have hKH : K ≤ H := CFSG.Quasithin.le_of_mem_cComp hK
  have hYH : Y ≤ H := uc22p20b_orb_le le_rfl hKH
  have hcC : CFSG.Quasithin.cComp Y = Set.range (fun t : H => uc22p20bCj (t : G) K) :=
    uc22p20b_cComp_orb hK le_rfl
  have hKi : ∀ i, uc22p20bCj (g i) K ∈ CFSG.Quasithin.cComp Y := fun i => by
    rw [hcC]; exact ⟨⟨g i, hg i⟩, rfl⟩
  have hKiY : ∀ i, uc22p20bCj (g i) K ≤ Y := fun i => CFSG.Quasithin.le_of_mem_cComp (hKi i)
  have hKisub : ∀ i, CFSG.Open.IsSubnormal (uc22p20bCj (g i) K) Y := fun i =>
    CFSG.Quasithin.subnormal_of_mem_cComp (hKi i)
  have hne : ∀ i j, i ≠ j → uc22p20bCj (g i) K ≠ uc22p20bCj (g j) K :=
    fun i j h h' => h (hinj h')
  have e : ∀ i, Bar2 K ≃* Bar2 (uc22p20bCj (g i) K) := fun i =>
    (uc22p20d_bar2_conj (g i) K).some
  have hPn : (CFSG.pCore 2 ↥Y).Normal := CFSG.pCore_normal
  let A : Fin 3 → Subgroup (↥Y ⧸ CFSG.pCore 2 ↥Y) := fun i =>
    ((uc22p20bCj (g i) K).subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
  have hcomm : ∀ i j, i ≠ j → ∀ a ∈ A i, ∀ b ∈ A j, a * b = b * a := fun i j hij =>
    uc22p20d_commute_images hO (hKi i) (hKi j) (hne i j hij)
  have hC : ∀ i j, i ≠ j → A i ≤ centralizer (A j : Set (↥Y ⧸ CFSG.pCore 2 ↥Y)) :=
    fun i j hij a ha => Subgroup.mem_centralizer_iff.2 fun b hb => (hcomm i j hij a ha b hb).symm
  have hmemA : ∀ (i : Fin 3) (c : ↥(uc22p20bCj (g i) K)),
      (QuotientGroup.mk (Subgroup.inclusion (hKiY i) c) : ↥Y ⧸ CFSG.pCore 2 ↥Y) ∈ A i :=
    fun i c => Subgroup.mem_map.2 ⟨Subgroup.inclusion (hKiY i) c,
      Subgroup.mem_subgroupOf.2 c.2, rfl⟩
  obtain ⟨hZ3, E', hE', hE'c⟩ := hU38 (Bar2 K) hU.1 (uc22p20p_odd_center_bar2 ↥K) hU.2
  obtain ⟨u, huE, huZ⟩ : ∃ u ∈ E', u ∉ center (Bar2 K) := by
    by_contra hcon
    push Not at hcon
    have hle : Nat.card E' ≤ Nat.card (center (Bar2 K)) := Subgroup.card_le_of_le hcon
    have h3 : Nat.card (center (Bar2 K)) ≤ 3 := Nat.le_of_dvd (by norm_num) hZ3
    rw [hE'c] at hle
    omega
  have hu3 : u ^ 3 = 1 := hE'.2 u huE
  have hsel : ∀ i, ∃ c : ↥(uc22p20bCj (g i) K),
      (QuotientGroup.mk c : Bar2 (uc22p20bCj (g i) K)) = e i u := fun i =>
    QuotientGroup.mk_surjective (e i u)
  choose c hc using hsel
  have hprops := fun i => uc22p20d_image_props (hKiY i) (hKisub i) (p := 3) (c i)
    (by rw [hc i, ← map_pow, hu3, map_one])
    (by rw [hc i]; exact uc22p20d_not_mem_center_map (e i) huZ)
  obtain ⟨e₀, -⟩ := uc22p20d_bar2Equiv (hKiY 0) (hKisub 0)
  obtain ⟨E₁, hE₁A, hE₁, hE₁c⟩ := uc22p20p_embed_rankWit ((e 0).trans e₀) ⟨E', hE', hE'c⟩
  have h12 := s208e_sup_zpowers Nat.prime_three (hmemA 1 (c 1)) (hprops 1).1 (hprops 1).2
    (hE₁A.trans (hC 0 1 (by decide))) hE₁ hE₁c
  have h123 := s208e_sup_zpowers Nat.prime_three (hmemA 2 (c 2)) (hprops 2).1 (hprops 2).2
    (sup_le (hE₁A.trans (hC 0 2 (by decide)))
      (((Subgroup.zpowers_le).2 (hmemA 1 (c 1))).trans (hC 1 2 (by decide)))) h12.1 h12.2
  obtain ⟨E, -, hE, hEc⟩ := uc22p20d_lift_elemAbelian (CFSG.pCore 2 ↥Y)
    (CFSG.pCore_isPGroup) Nat.prime_three (by norm_num) (⊤ : Subgroup ↥Y) _ h123.1 h123.2
    (by rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)]; exact le_top)
  refine ⟨E.map Y.subtype, (Subgroup.map_subtype_le E).trans hYH,
    uc22p20d_isElemAbelian_map Y.subtype Y.subtype_injective hE, ?_⟩
  rw [Subgroup.card_map_of_injective Y.subtype_injective, hEc]

theorem s208e_one_le_pRank {X : Subgroup G} {n : ℕ} (hn : 2 < n)
    (h : IsSz (Bar2 X) n ∨ IsL2 (Bar2 X) n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    1 ≤ CFSG.Open.pRank p X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← s208e_pRank_bar X hp (s208e_ne_two hpn (by omega))]
  obtain ⟨P⟩ : Nonempty (Sylow 2 (Bar2 X)) := inferInstance
  obtain ⟨x, -, hxo, -⟩ := s208e_borel_prop hn h hp hpn P
  exact CFSG.SectionRank.le_pRank hp.one_lt (le_top : zpowers x ≤ ⊤)
    (s208e_isElemAbelian_zpowers (hxo ▸ pow_orderOf_eq_one x))
    (by rw [Nat.card_zpowers, hxo, pow_one])

private theorem s208e_prod_borel {Y : Type} [Group Y] [Finite Y] {n : ℕ} (hn : 2 < n)
    (h : IsSzL2Product Y n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1)
    {S : Subgroup Y} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S ⊤) :
    ∃ F : Subgroup Y, F ≤ normalizer (S : Set Y) ∧ IsElemAbelian p F ∧ Nat.card F = p ^ 2 := by
  obtain ⟨A, B, _, _, ⟨e⟩, hA, hB⟩ := h
  have : Finite A := Finite.of_injective (fun a : A => e.symm (a, 1)) fun a b hab => by
    simpa using congrArg Prod.fst (e.symm.injective hab)
  have : Finite B := Finite.of_injective (fun b : B => e.symm (1, b)) fun a b hab => by
    simpa using congrArg Prod.snd (e.symm.injective hab)
  let f₁ : A →* Y := e.symm.toMonoidHom.comp (MonoidHom.inl A B)
  let f₂ : B →* Y := e.symm.toMonoidHom.comp (MonoidHom.inr A B)
  have hf₁ : Function.Injective f₁ := fun a b hab => by
    simpa using congrArg Prod.fst (e.symm.injective hab)
  have hf₂ : Function.Injective f₂ := fun a b hab => by
    simpa using congrArg Prod.snd (e.symm.injective hab)
  have hcomm : ∀ x ∈ f₁.range, ∀ y ∈ f₂.range, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply,
      MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one]
  have hcomm' : ∀ y ∈ f₂.range, ∀ x ∈ f₁.range, y * x = x * y :=
    fun y hy x hx => (hcomm x hx y hy).symm
  have hsup : f₁.range ⊔ f₂.range = ⊤ := by
    rw [eq_top_iff]
    intro y _
    have hy : y = f₁ (e y).1 * f₂ (e y).2 := by
      simp only [f₁, f₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MonoidHom.inl_apply,
        MonoidHom.inr_apply, ← map_mul, Prod.mk_mul_mk, one_mul, mul_one, Prod.mk.eta,
        MulEquiv.symm_apply_apply]
    rw [hy]
    exact Subgroup.mul_mem_sup ⟨_, rfl⟩ ⟨_, rfl⟩
  have hsup' : f₂.range ⊔ f₁.range = ⊤ := by rw [sup_comm, hsup]
  have hdisj : ∀ x ∈ f₁.range ⊓ f₂.range, x ^ p = 1 → x = 1 := by
    rintro x ⟨⟨a, rfl⟩, ⟨b, hb⟩⟩ -
    have h1 : (1 : A) = a := congrArg Prod.fst (e.symm.injective hb)
    rw [← h1, map_one]
  have hW : ∀ (Z : Type) [Group Z] [Finite Z], (IsSz Z n ∨ IsL2 Z n) →
      uc22p20oBorelWit Z p 1 := by
    intro Z _ _ hZ P
    obtain ⟨x, hxN, hxo, -⟩ := s208e_borel_prop hn hZ hp hpn P
    exact ⟨zpowers x, (Subgroup.zpowers_le).2 hxN,
      s208e_isElemAbelian_zpowers (hxo ▸ pow_orderOf_eq_one x),
      by rw [Nat.card_zpowers, hxo, pow_one]⟩
  obtain ⟨F₁, hF₁A, hF₁N, hF₁, hF₁c⟩ := uc22p20p_embed_borelWit (MonoidHom.ofInjective hf₁)
    (uc22p20p_isSylowOf_inf_left hcomm hsup hS) (hW A hA)
  obtain ⟨F₂, hF₂A, hF₂N, hF₂, hF₂c⟩ := uc22p20p_embed_borelWit (MonoidHom.ofInjective hf₂)
    (uc22p20p_isSylowOf_inf_left hcomm' hsup' hS) (hW B hB)
  obtain ⟨hF, hFc⟩ := uc22p20p_sup_elemAbelian hcomm hF₁A hF₂A hF₁ hF₂ hF₁c hF₂c hdisj
  exact ⟨F₁ ⊔ F₂, sup_le
    (fun x hx => uc22p20p_normalizer_of_split hcomm hsup hS (hF₁A hx) (hF₁N hx))
    (fun x hx => uc22p20p_normalizer_of_split hcomm' hsup' hS (hF₂A hx) (hF₂N hx)), hF, hFc⟩

theorem s208e_two_le_pRank {X : Subgroup G} {n : ℕ} (hn : 2 < n)
    (h : IsSzL2Product (Bar2 X) n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    2 ≤ CFSG.Open.pRank p X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [← s208e_pRank_bar X hp (s208e_ne_two hpn (by omega))]
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (⊤ : Subgroup (Bar2 X))
  obtain ⟨F, -, hF, hFc⟩ := s208e_prod_borel hn h hp hpn hS
  exact CFSG.SectionRank.le_pRank hp.one_lt le_top hF hFc

theorem s208e_two_le_pRank_borel (D : Data G) (hB : ListBNonabelian) (h1930 : H1930 D)
    {L' : Subgroup G} (hL' : L' ∈ calL D.T D.M) {n : ℕ} (hn : 2 < n)
    (h : IsSzL2Product (Bar2 L') n) {p : ℕ} (hp : p.Prime) (hpn : p ∣ 2 ^ n - 1) :
    2 ≤ CFSG.Open.pRank p ((L' ⊔ D.T) ⊓ D.M) := by
  obtain ⟨F, hFN, hF, hFc⟩ := s208e_prod_borel hn h hp hpn (uc22p20p_sylowBar_isSylowOf D hL')
  exact (CFSG.SectionRank.le_pRank hp.one_lt hFN hF hFc).trans
    (uc22p20i_pRank_borel_le D hB h1930 hL' hp (s208e_ne_two hpn (by omega)))

end CFSG.LocalAnalysis.UniquenessCase.UC22
