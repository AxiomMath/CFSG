module

public import CFSG.Quasithin.Background.P3G2Data
public import CFSG.Quasithin.Background.P3G2Zorn
public import CFSG.LinearAlgebra.LinearGroups.UnitaryThreeOverNineGroups

public section

namespace CFSG.Quasithin.G11.P3G2

open Matrix CFSG.Assembly.LowTwoRank CFSG.Open CFSG.Quasithin.Explicit
  CFSG.Quasithin.JonesParshall CFSG.Quasithin.G2U

instance finiteF9 : Finite F9 :=
  Finite.of_equiv _ (QuadraticAlgebra.equivProd (-1 : ZMod 3) 0).symm

@[expose] def gAi3 : ℕ := 590499

@[expose] def gBi3 : ℕ := 266868585

@[expose] def unitOf (m mi : ℕ) (h1 : matDec3 m * matDec3 mi = 1)
    (h2 : matDec3 mi * matDec3 m = 1) : GL (Fin 3) F9 :=
  ⟨matDec3 m, matDec3 mi, h1, h2⟩

@[expose] def AU : GL (Fin 3) F9 :=
  unitOf gA3 gAi3 (by decide +kernel) (by decide +kernel)

@[expose] def BU : GL (Fin 3) F9 :=
  unitOf gB3 gBi3 (by decide +kernel) (by decide +kernel)

theorem matA2_eq : matA2 = matDec8 gA8 := by
  decide +kernel

theorem matB2_eq : matB2 = matDec8 gB8 := by
  decide +kernel

abbrev PairGroup : Type :=
  ↥(cayleyGroup (ZMod 2)) × GL (Fin 3) F9

@[expose] noncomputable def fHom :
    PairGroup →* Matrix (Fin 8) (Fin 8) (ZMod 2) × Matrix (Fin 3) (Fin 3) F9 :=
  (cmat (F := ZMod 2)).prodMap (Units.coeHom (Matrix (Fin 3) (Fin 3) F9))

theorem fHom_injective : Function.Injective fHom := by
  intro x y h
  exact Prod.ext (cmat_injective (congrArg Prod.fst h)) (Units.val_injective (congrArg Prod.snd h))

@[expose] def genSet : Set PairGroup :=
  {(g2a, AU), (g2b, BU)}

theorem fHom_genSet :
    fHom '' genSet = {GAp, GBp} := by
  have h1 : fHom (g2a, AU) = GAp := by
    show (cmat g2a, ((AU : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9)) =
      (matDec8 gA8, matDec3 gA3)
    rw [cmat_g2a, matA2_eq]
    rfl
  have h2 : fHom (g2b, BU) = GBp := by
    show (cmat g2b, ((BU : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9)) =
      (matDec8 gB8, matDec3 gB3)
    rw [cmat_g2b, matB2_eq]
    rfl
  rw [genSet, Set.image_pair, h1, h2]

@[expose] noncomputable def pairD : Subgroup PairGroup :=
  Subgroup.closure genSet

theorem card_pairD :
    Nat.card pairD = 6048 :=
  cert_card decK_rmulA decK_rmulB certData_ok certData_root fHom fHom_injective genSet fHom_genSet

theorem pairD_graph
    {g : PairGroup} (hg : g ∈ pairD) : ((fHom g).1 = 1 ↔ (fHom g).2 = 1) :=
  cert_graph decK_rmulA decK_rmulB certData_ok certData_root fHom genSet fHom_genSet hg

theorem pairD_fst_one
    {g : PairGroup} (hg : g ∈ pairD) (h : g.1 = 1) : g.2 = 1 := by
  have h1 : (fHom g).1 = 1 := by
    show cmat g.1 = 1
    rw [h, map_one]
  exact Units.ext ((pairD_graph hg).mp h1)

theorem pairD_snd_one
    {g : PairGroup} (hg : g ∈ pairD) (h : g.2 = 1) : g.1 = 1 := by
  have h2 : (fHom g).2 = 1 := by
    show ((g.2 : GL (Fin 3) F9) : Matrix (Fin 3) (Fin 3) F9) = 1
    rw [h]
    rfl
  exact cmat_injective (((pairD_graph hg).mpr h2).trans (map_one (cmat (F := ZMod 2))).symm)

@[expose] noncomputable def jSub : Subgroup ↥(cayleyGroup (ZMod 2)) :=
  Subgroup.closure {g2a, g2b}

@[expose] noncomputable def sSub : Subgroup (GL (Fin 3) F9) :=
  Subgroup.closure {AU, BU}

theorem map_fst_pairD : pairD.map (MonoidHom.fst _ _) = jSub := by
  rw [pairD, MonoidHom.map_closure, genSet, Set.image_pair]
  rfl

theorem map_snd_pairD : pairD.map (MonoidHom.snd _ _) = sSub := by
  rw [pairD, MonoidHom.map_closure, genSet, Set.image_pair]
  rfl

noncomputable def pairDEquivJ
    : pairD ≃* jSub :=
  (MulEquiv.ofBijective ((MonoidHom.fst _ _).subgroupMap pairD)
    ⟨(injective_iff_map_eq_one _).mpr fun x hx => by
      have h1 : x.1.1 = 1 := congrArg Subtype.val hx
      exact Subtype.ext (Prod.ext h1 (pairD_fst_one x.2 h1)),
      MonoidHom.subgroupMap_surjective _ _⟩).trans (MulEquiv.subgroupCongr map_fst_pairD)

noncomputable def pairDEquivS
    : pairD ≃* sSub :=
  (MulEquiv.ofBijective ((MonoidHom.snd _ _).subgroupMap pairD)
    ⟨(injective_iff_map_eq_one _).mpr fun x hx => by
      have h2 : x.1.2 = 1 := congrArg Subtype.val hx
      exact Subtype.ext (Prod.ext (pairD_snd_one x.2 h2) h2),
      MonoidHom.subgroupMap_surjective _ _⟩).trans (MulEquiv.subgroupCongr map_snd_pairD)

private theorem mem_statedSU_of_codes (m mi : ℕ) (h1 : matDec3 m * matDec3 mi = 1)
    (h2 : matDec3 mi * matDec3 m = 1)
    (h : ((matDec3 m).map (· ^ 3))ᵀ * matDec3 m = 1 ∧ (matDec3 m).det = 1) :
    unitOf m mi h1 h2 ∈ StatedSU 3 3 F9 := by
  rw [← SetLike.mem_coe, LinearGroups.UnitaryThreeOverNine.coe_statedSU card_F9]
  exact h

theorem sSub_eq :
    sSub = StatedSU 3 3 F9 := by
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · rw [sSub, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact mem_statedSU_of_codes _ _ _ _ (by rw [Matrix.det_fin_three]; decide +kernel)
    · exact mem_statedSU_of_codes _ _ _ _ (by rw [Matrix.det_fin_three]; decide +kernel)
  · rw [LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9,
      ← Nat.card_congr pairDEquivS.toEquiv, card_pairD]

theorem jSub_map : jSub.map (cayleyGroup (ZMod 2)).subtype = subG2 := by
  rw [jSub, MonoidHom.map_closure, Set.image_pair]
  rfl

noncomputable def subG2EquivSU :
    ↥subG2 ≃* StatedSU 3 3 F9 :=
  (((Subgroup.equivMapOfInjective jSub (cayleyGroup (ZMod 2)).subtype
    Subtype.val_injective).trans (MulEquiv.subgroupCongr jSub_map)).symm.trans
      pairDEquivJ.symm).trans (pairDEquivS.trans (MulEquiv.subgroupCongr sSub_eq))

noncomputable def commutatorG2EquivSU :
    ↥⁅quasithinG2 (GaloisField 2 1), quasithinG2 (GaloisField 2 1)⁆ ≃*
      StatedSU 3 3 F9 :=
  commutatorG2Equiv.trans subG2EquivSU

theorem card_commutatorG2 :
    Nat.card ↥⁅quasithinG2 (GaloisField 2 1), quasithinG2 (GaloisField 2 1)⁆ = 6048 := by
  rw [Nat.card_congr commutatorG2EquivSU.toEquiv,
    LinearGroups.UnitaryThreeOverNine.card_statedSU card_F9]

end CFSG.Quasithin.G11.P3G2
