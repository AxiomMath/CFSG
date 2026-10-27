module

public import CFSG.LocalAnalysis.StandardType.GGSporKLieZDefs
public import CFSG.Open.GLADefs
import CFSG.LocalAnalysis.GLTheoremA.CatA.I142NTrans
import CFSG.LocalAnalysis.AGLEmbedding.CZeroSubnormalCommute
import CFSG.LocalAnalysis.AGLEmbedding.CZeroDefs
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PCoreFreeFixedPointsCentralize
import CFSG.Walter.Bender1970.S2.TwoSubgroup
import CFSG.Walter.PSL2Facts
import Certificates.Certificate1
import Certificates.Certificate2

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.Open CFSG.Assembly

@[expose] def PCoreSevenTrivial (R : Type*) [Group R] : Prop :=
  ∀ x : R, orderOf x = 7 → pCoreOf 2 (Subgroup.centralizer ({x} : Set R)) = ⊥

private lemma l937z_rd_centralizer_map_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (x : G) :
    Subgroup.centralizer ({(e x)} : Set H) =
      (Subgroup.centralizer ({x} : Set G)).map e.toMonoidHom := by
  ext y
  constructor
  · intro hy
    refine Subgroup.mem_map.mpr ⟨e.symm y, ?_, by simp⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h := (Subgroup.mem_centralizer_iff.mp hy) (e x) (Set.mem_singleton _)
    simpa using congrArg e.symm h
  · rintro ⟨y, hy, rfl⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    have h := (Subgroup.mem_centralizer_iff.mp hy) x (Set.mem_singleton _)
    simpa using congrArg e h

private lemma l937z_rd_pCoreOf_map_mulEquiv {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (K : Subgroup G) :
    pCoreOf 2 (K.map e.toMonoidHom) = (pCoreOf 2 K).map e.toMonoidHom := by
  let f : G →* H := e.toMonoidHom
  let eK : ↥K ≃* ↥(K.map f) := K.equivMapOfInjective f e.injective
  have hcomp : (K.map f).subtype.comp eK.toMonoidHom = f.comp K.subtype := by
    ext k
    rfl
  calc
    pCoreOf 2 (K.map f) = (CFSG.pCore 2 ↥(K.map f)).map (K.map f).subtype := rfl
    _ = ((CFSG.pCore 2 ↥K).map eK.toMonoidHom).map (K.map f).subtype := by
          rw [CFSG.pCore_map_iso 2 eK]
    _ = (CFSG.pCore 2 ↥K).map ((K.map f).subtype.comp eK.toMonoidHom) :=
          Subgroup.map_map (CFSG.pCore 2 ↥K) (K.map f).subtype eK.toMonoidHom
    _ = (CFSG.pCore 2 ↥K).map (f.comp K.subtype) := by rw [hcomp]
    _ = ((CFSG.pCore 2 ↥K).map K.subtype).map f :=
          (Subgroup.map_map (CFSG.pCore 2 ↥K) f K.subtype).symm
    _ = (pCoreOf 2 K).map f := rfl

theorem pCoreSevenTrivial_of_mulEquiv {R R' : Type*} [Group R] [Group R'] (e : R ≃* R')
    (h : PCoreSevenTrivial R) : PCoreSevenTrivial R' := by
  intro x' hx'
  have hx : orderOf (e.symm x') = 7 := by
    change orderOf (e.symm.toMonoidHom x') = 7
    rw [orderOf_injective e.symm.toMonoidHom e.symm.injective, hx']
  have hh : pCoreOf 2 (Subgroup.centralizer ({e.symm x'} : Set R)) = ⊥ := h (e.symm x') hx
  have hmap := l937z_rd_pCoreOf_map_mulEquiv e (Subgroup.centralizer ({e.symm x'} : Set R))
  rw [hh, Subgroup.map_bot] at hmap
  rw [← l937z_rd_centralizer_map_mulEquiv e (e.symm x')] at hmap
  simpa using hmap

theorem lieZRow_of_pCoreSevenTrivial {R : Type} [Group R] [Finite R]
    (h : PCoreSevenTrivial R) : LieZRow R := by
  intro x hx J hJ
  rw [← Nat.not_even_iff_odd]
  intro heven
  rw [even_iff_two_dvd] at heven
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 2 heven
  let Z : Subgroup R := J ⊓ Subgroup.centralizer (J : Set R)
  have hzord0 : orderOf (z : R) = 2 := by
    change orderOf (Z.subtype z) = 2
    rw [orderOf_injective Z.subtype Z.subtype_injective, hzord]
  have hzJ : (z : R) ∈ J := z.2.1
  have hzC : (z : R) ∈ Subgroup.centralizer (J : Set R) := z.2.2
  let T : Subgroup R := Subgroup.zpowers (z : R)
  have hTJ : T ≤ J := Subgroup.zpowers_le.mpr hzJ
  have hTC : T ≤ Subgroup.centralizer (J : Set R) := Subgroup.zpowers_le.mpr hzC
  have hTp : IsPGroup 2 T := by
    refine IsPGroup.of_card (n := 1) ?_
    change Nat.card ↥(Subgroup.zpowers (z : R)) = 2 ^ 1
    rw [Nat.card_zpowers, hzord0]
    norm_num
  have hTnorm : (T.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTJ).mpr <|
      (Subgroup.le_centralizer_iff.mpr hTC).trans (Subgroup.centralizer_le_normalizer (T : Set R))
  have hTD : Assembly.IsSubnormal T (Subgroup.centralizer ({x} : Set R)) :=
    Assembly.IsSubnormal.step hTJ hTnorm hJ.2.1
  have hTDopen : Open.IsSubnormal T (Subgroup.centralizer ({x} : Set R)) :=
    (CFSG.Assembly.isSubnormal_iff_open).mp hTD
  have hTle : T ≤ pCoreOf 2 (Subgroup.centralizer ({x} : Set R)) :=
    CFSG.AGLEmbedding.SubnormalCommute.le_pCoreOf_of_isSubnormal hTDopen hTp
  rw [h x hx] at hTle
  have hzT : (z : R) ∈ T := Subgroup.mem_zpowers _
  have hz1 : (z : R) = 1 := by simpa using hTle hzT
  rw [hz1, orderOf_one] at hzord0
  exact (by norm_num : (1 : ℕ) ≠ 2) hzord0

@[expose] def LayerCentreSeven (R : Type*) [Group R] : Prop :=
  ∀ x : R, orderOf x = 7 → ∀ z ∈ GLALayer (Subgroup.centralizer ({x} : Set R)),
    (∀ y ∈ GLALayer (Subgroup.centralizer ({x} : Set R)), z * y = y * z) → z ^ 2 = 1 → z = 1

theorem lieZRow_of_layerCentreSeven {R : Type} [Group R] [Finite R]
    (h : LayerCentreSeven R) : LieZRow R := by
  intro x hx J hJ
  rw [← Nat.not_even_iff_odd]
  intro heven
  rw [even_iff_two_dvd] at heven
  obtain ⟨z, hzord⟩ := exists_prime_orderOf_dvd_card' 2 heven
  let Z : Subgroup R := J ⊓ Subgroup.centralizer (J : Set R)
  have hzord0 : orderOf (z : R) = 2 := by
    change orderOf (Z.subtype z) = 2
    rw [orderOf_injective Z.subtype Z.subtype_injective, hzord]
  have hJopen : Open.IsComponentOf J (Subgroup.centralizer ({x} : Set R)) :=
    (CFSG.Assembly.isComponentOf_iff_open).mp hJ
  have hzG : (z : R) ∈ GLALayer (Subgroup.centralizer ({x} : Set R)) :=
    CFSG.LocalAnalysis.GLTheoremA.I142N.le_GLALayer hJopen z.2.1
  have hle : GLALayer (Subgroup.centralizer ({x} : Set R)) ≤
      Subgroup.centralizer ({(z : R)} : Set R) := by
    refine CFSG.LocalAnalysis.GLTheoremA.I142N.GLALayer_le_of ?_
    intro K hK k hk
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    rcases CFSG.LocalAnalysis.GLTheoremA.I142N.isComponent_commute_or_eq hK hJopen with
      rfl | hcomm
    · exact ((Subgroup.mem_centralizer_iff.mp z.2.2) k hk).symm
    · exact (Subgroup.mem_centralizer_iff.mp
        ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hk)) (z : R) z.2.1
  have hzcent : ∀ y ∈ GLALayer (Subgroup.centralizer ({x} : Set R)),
      (z : R) * y = y * (z : R) := by
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hle hy)) (z : R) (Set.mem_singleton _)
  have hzsq : (z : R) ^ 2 = 1 := by
    rw [← hzord0]
    exact pow_orderOf_eq_one _
  have hz1 : (z : R) = 1 := h x hx (z : R) hzG hzcent hzsq
  rw [hz1, orderOf_one] at hzord0
  exact (by norm_num : (1 : ℕ) ≠ 2) hzord0

private lemma l937z_rd_pCore_eq_bot_of_mulEquiv {p : ℕ} {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : CFSG.pCore p G = ⊥) : CFSG.pCore p H = ⊥ := by
  have hmap : (CFSG.pCore p H).map e.symm.toMonoidHom = (⊥ : Subgroup G) := by
    rw [CFSG.pCore_map_iso p e.symm, h]
  rw [Subgroup.map_eq_bot_iff] at hmap
  apply le_bot_iff.mp
  intro x hx
  have h1 : e.symm.toMonoidHom x = 1 := (MonoidHom.mem_ker).mp (hmap hx)
  exact (MulEquiv.map_eq_one_iff e.symm).mp h1

private lemma l937z_rd_pCore_pi_eq_bot {p : ℕ} {ι : Type*} {M : ι → Type*}
    [∀ i, Group (M i)] (h : ∀ i, CFSG.pCore p (M i) = ⊥) :
    CFSG.pCore p (∀ i, M i) = ⊥ := by
  apply le_bot_iff.mp
  intro x hx
  funext i
  have hsurj : Function.Surjective (Pi.evalMonoidHom M i) := by
    intro m
    classical
    exact ⟨Function.update 1 i m, by simp⟩
  have hnormal : (Subgroup.map (Pi.evalMonoidHom M i)
      (CFSG.pCore p (∀ i, M i))).Normal :=
    Subgroup.Normal.map (CFSG.pCore_normal (p := p) (G := ∀ i, M i))
      (Pi.evalMonoidHom M i) hsurj
  have hp : IsPGroup p ↥(Subgroup.map (Pi.evalMonoidHom M i)
      (CFSG.pCore p (∀ i, M i))) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := p) (G := ∀ i, M i))
      (Pi.evalMonoidHom M i)
  have hle : Subgroup.map (Pi.evalMonoidHom M i) (CFSG.pCore p (∀ i, M i)) ≤
      CFSG.pCore p (M i) := by
    change Subgroup.map (Pi.evalMonoidHom M i) (CFSG.pCore p (∀ i, M i)) ≤
      sSup {K : Subgroup (M i) | K.Normal ∧ IsPGroup p K}
    exact le_sSup ⟨hnormal, hp⟩
  rw [h i] at hle
  have hxmem : Pi.evalMonoidHom M i x ∈
      Subgroup.map (Pi.evalMonoidHom M i) (CFSG.pCore p (∀ i, M i)) :=
    Subgroup.mem_map_of_mem _ hx
  have := hle hxmem
  simpa using this

theorem pCore_trivial_of_commutingProduct {G : Type} [Group G] [Finite G] (C : Subgroup G)
    {ι : Type} (s : Finset ι) (Gs : ι → Subgroup G)
    (hle : ∀ i ∈ s, Gs i ≤ C)
    (hcomm : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → ∀ x ∈ Gs i, ∀ y ∈ Gs j, Commute x y)
    (hsup : (⨆ i ∈ s, Gs i) = C) (hcard : Nat.card C = ∏ i ∈ s, Nat.card (Gs i))
    (hO2 : ∀ i ∈ s, pCoreOf 2 (Gs i) = ⊥) : pCoreOf 2 C = ⊥ := by
  classical
  let H : ↥s → Subgroup G := fun i => Gs i.1
  have hcomm' : Pairwise fun i j : ↥s => ∀ x y : G, x ∈ H i → y ∈ H j → Commute x y := by
    intro i j hij x y hx hy
    exact hcomm i.1 i.2 j.1 j.2 (fun h => hij (Subtype.ext h)) x hx y hy
  let φ : ((i : ↥s) → ↥(H i)) →* G := Subgroup.noncommPiCoprod hcomm'
  have hφrange : φ.range = ⨆ i : ↥s, H i := Subgroup.noncommPiCoprod_range
  have hsup' : (⨆ i : ↥s, H i) = C := by
    rw [iSup_subtype]
    exact hsup
  have hrange : φ.range = C := hφrange.trans hsup'
  have hle_iSup : (⨆ i : ↥s, H i) ≤ C := iSup_le fun i => hle i.1 i.2
  have hφmem : ∀ a, φ a ∈ C := fun a =>
    hle_iSup (by rw [← hφrange]; exact ⟨a, rfl⟩)
  let φc : ((i : ↥s) → ↥(H i)) →* ↥C := φ.codRestrict C hφmem
  have hφc_surj : Function.Surjective φc := by
    intro c
    have hc : (c : G) ∈ φ.range := by rw [hrange]; exact c.2
    rcases hc with ⟨a, ha⟩
    refine ⟨a, ?_⟩
    rw [MonoidHom.codRestrict_apply]
    exact Subtype.ext ha
  have hcard' : Nat.card ((i : ↥s) → ↥(H i)) = Nat.card ↥C := by
    rw [Nat.card_pi]
    exact (Finset.prod_coe_sort s (fun i => Nat.card ↥(Gs i))).trans (by rw [← hcard])
  let e : ((i : ↥s) → ↥(H i)) ≃* ↥C :=
    MulEquiv.ofBijective φc ((Nat.bijective_iff_surjective_and_card φc).mpr ⟨hφc_surj, hcard'⟩)
  have hdom : CFSG.pCore 2 ((i : ↥s) → ↥(H i)) = ⊥ := by
    apply l937z_rd_pCore_pi_eq_bot
    intro i
    have hOi : pCoreOf 2 (Gs i.1) = ⊥ := hO2 i.1 i.2
    have hmap : (CFSG.pCore 2 ↥(Gs i.1)).map (Gs i.1).subtype = ⊥ := hOi
    rw [Subgroup.map_eq_bot_iff] at hmap
    apply le_bot_iff.mp
    intro x hx
    have hx1 : (Gs i.1).subtype x = 1 := (MonoidHom.mem_ker).mp (hmap hx)
    exact Subtype.ext (by simpa using hx1)
  have hC : CFSG.pCore 2 ↥C = ⊥ := l937z_rd_pCore_eq_bot_of_mulEquiv e hdom
  change (CFSG.pCore 2 ↥C).map C.subtype = ⊥
  rw [hC, Subgroup.map_bot]

theorem pCore_trivial_pi {ι : Type} [Finite ι] {M : ι → Type} [∀ i, Group (M i)] [∀ i, Finite (M i)]
    (h : ∀ i, pCore 2 (M i) = ⊥) : pCore 2 (∀ i, M i) = ⊥ :=
  l937z_rd_pCore_pi_eq_bot h

theorem pCore_trivial_of_mulEquiv {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (h : pCore 2 G = ⊥) : pCore 2 H = ⊥ :=
  l937z_rd_pCore_eq_bot_of_mulEquiv e h

end CFSG.StandardType.SporadicShape
