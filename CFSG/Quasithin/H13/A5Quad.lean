module

public import CFSG.Quasithin.H13.A5Quad8
public import CFSG.Quasithin.Background.B5FinG2U33
public import CFSG.Quasithin.Background.P3G2Zorn
public import CFSG.Quasithin.Background.B5Models
public import Certificates.Certificate17028
public import Certificates.Certificate8952
public import Certificates.Certificate8953
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Fischer.Pairs
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42Transport
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C127Main
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure312Defs
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure37Base
public import CFSG.Quasithin.Background.A3Structure37Comm
public import CFSG.Quasithin.Background.A3Structure37Frattini
public import CFSG.Quasithin.Background.A3Structure37KeyBase
public import CFSG.Quasithin.Background.A3Structure37Schur
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.S142Statements
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5S1520a
public import CFSG.Quasithin.H13.A5S1520c
public import CFSG.Quasithin.H13.A5S1520d
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch1Prop121
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Transvection.Statement
public import Certificates.Certificate8026Base

public section

namespace CFSG.Quasithin.H13.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.JonesParshall
  CFSG.Quasithin.Explicit CFSG.Assembly.LowTwoRank
open scoped Matrix

section Coord

@[expose] def rVec : Fin 8 → ZMod 2 := ![1, 0, 0, 0, 0, 0, 0, 1]

@[expose] def baseVec : Fin 8 → ZMod 2 := ![0, 1, 0, 0, 0, 0, 0, 0]

@[expose] def g2M : Fin 2 → Matrix (Fin 8) (Fin 8) (ZMod 2) := ![matA2, matB2]

@[expose] def wordAct (w : List (Fin 2)) (v : Fin 8 → ZMod 2) : Fin 8 → ZMod 2 :=
  w.foldr (fun i v => g2M i *ᵥ v) v

@[expose] def g2Table : List ((Fin 8 → ZMod 2) × List (Fin 2)) :=
  [(![0, 0, 0, 0, 0, 0, 1, 0], [0, 1, 0, 0, 1, 0, 0]),
    (![0, 0, 0, 0, 0, 1, 0, 0], [1, 0, 1, 0, 0, 1, 0, 0]),
    (![0, 0, 0, 0, 0, 1, 1, 0], [1, 1, 0, 1, 0, 0, 1, 0, 0]),
    (![0, 0, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 1, 0]),
    (![0, 0, 0, 0, 1, 0, 1, 0], [1, 1, 0, 0, 1, 1, 0]),
    (![0, 0, 0, 0, 1, 1, 0, 0], [0, 1, 0, 0, 1, 0, 0, 1, 0, 0]),
    (![0, 0, 0, 0, 1, 1, 1, 0], [0, 0, 1, 1, 0]),
    (![0, 0, 0, 1, 0, 0, 0, 0], [0, 1, 0]),
    (![0, 0, 0, 1, 0, 0, 1, 0], [1, 0, 0]),
    (![0, 0, 0, 1, 0, 1, 0, 0], [1, 1, 0, 1, 1, 0]),
    (![0, 0, 0, 1, 0, 1, 1, 0], [1, 0]),
    (![0, 0, 0, 1, 1, 0, 0, 0], [0, 0, 1, 0, 1, 1, 0]),
    (![0, 0, 0, 1, 1, 0, 1, 0], [1, 0, 1, 0, 0]),
    (![0, 0, 0, 1, 1, 1, 0, 0], [0, 0, 1, 0, 1, 0, 0]),
    (![0, 0, 0, 1, 1, 1, 1, 0], [0, 1, 1, 0, 1, 0]),
    (![0, 0, 1, 0, 0, 0, 0, 0], [0, 1, 0, 1, 1, 0, 0]),
    (![0, 0, 1, 0, 0, 0, 1, 0], [0, 1, 1, 0, 1, 0, 0]),
    (![0, 0, 1, 0, 0, 1, 0, 0], [1, 0, 0, 1, 0, 0]),
    (![0, 0, 1, 0, 0, 1, 1, 0], [0, 0, 1, 0, 0, 1, 0, 0]),
    (![0, 0, 1, 0, 1, 0, 0, 0], [0, 1, 1, 0, 0]),
    (![0, 0, 1, 0, 1, 0, 1, 0], [0, 0, 1, 0, 1, 0]),
    (![0, 0, 1, 0, 1, 1, 0, 0], [0, 1, 0, 0, 1, 1, 0]),
    (![0, 0, 1, 0, 1, 1, 1, 0], [0, 0, 1, 0, 0, 1, 1, 0]),
    (![0, 0, 1, 1, 0, 0, 0, 0], [1, 0, 1, 0, 1, 0]),
    (![0, 0, 1, 1, 0, 0, 1, 0], [0, 0, 1, 0, 0]),
    (![0, 0, 1, 1, 0, 1, 0, 0], [0, 1, 0, 1, 0, 1, 0]),
    (![0, 0, 1, 1, 0, 1, 1, 0], [0, 1, 1, 0, 1, 1, 0]),
    (![0, 0, 1, 1, 1, 0, 0, 0], [0, 1, 0, 1, 1, 0]),
    (![0, 0, 1, 1, 1, 0, 1, 0], [0, 1, 0, 1, 0, 1, 0, 0]),
    (![0, 0, 1, 1, 1, 1, 0, 0], [0, 0, 1, 1, 0, 1, 0]),
    (![0, 0, 1, 1, 1, 1, 1, 0], [1, 1, 0, 1, 1, 0, 0]),
    (![0, 1, 0, 0, 0, 0, 0, 0], []),
    (![0, 1, 0, 0, 0, 0, 1, 0], [1, 1, 0, 1, 0, 1, 0, 0]),
    (![0, 1, 0, 0, 0, 1, 0, 0], [0, 1, 0, 1, 0, 0]),
    (![0, 1, 0, 0, 0, 1, 1, 0], [1, 0, 1, 0, 1, 0, 0]),
    (![0, 1, 0, 0, 1, 0, 0, 0], [1, 0, 0, 1, 0]),
    (![0, 1, 0, 0, 1, 0, 1, 0], [1, 1, 0, 0, 1, 0]),
    (![0, 1, 0, 0, 1, 1, 0, 0], [0, 0, 1, 0, 1, 0, 1, 0]),
    (![0, 1, 0, 0, 1, 1, 1, 0], [0, 0, 1, 0]),
    (![0, 1, 0, 1, 0, 0, 0, 0], [0, 1, 0, 1, 0]),
    (![0, 1, 0, 1, 0, 0, 1, 0], [1, 0, 0, 1, 0, 0, 1, 0, 0]),
    (![0, 1, 0, 1, 0, 1, 0, 0], [1, 0, 1, 1, 0, 1, 0, 0]),
    (![0, 1, 0, 1, 0, 1, 1, 0], [0, 0, 1, 1, 0, 0]),
    (![0, 1, 0, 1, 1, 0, 0, 0], [0, 1, 0, 0, 1, 0, 1, 0]),
    (![0, 1, 0, 1, 1, 0, 1, 0], [1, 0, 1, 1, 0, 0]),
    (![0, 1, 0, 1, 1, 1, 0, 0], [0, 0, 1, 1, 0, 1, 0, 0]),
    (![0, 1, 0, 1, 1, 1, 1, 0], [1, 0, 0, 1, 0, 1, 0]),
    (![0, 1, 1, 0, 0, 0, 0, 0], [1, 1, 0, 1, 0]),
    (![0, 1, 1, 0, 0, 0, 1, 0], [1, 0, 1, 1, 0]),
    (![0, 1, 1, 0, 0, 1, 0, 0], [0]),
    (![0, 1, 1, 0, 0, 1, 1, 0], [0, 0]),
    (![0, 1, 1, 0, 1, 0, 0, 0], [0, 1, 0, 0]),
    (![0, 1, 1, 0, 1, 0, 1, 0], [1, 1, 0, 1, 1, 0, 1, 0]),
    (![0, 1, 1, 0, 1, 1, 0, 0], [0, 0, 1, 1, 0, 0, 1, 0]),
    (![0, 1, 1, 0, 1, 1, 1, 0], [0, 1, 1, 0, 0, 1, 0]),
    (![0, 1, 1, 1, 0, 0, 0, 0], [1, 0, 1, 0]),
    (![0, 1, 1, 1, 0, 0, 1, 0], [1, 1, 0]),
    (![0, 1, 1, 1, 0, 1, 0, 0], [1, 1, 0, 0]),
    (![0, 1, 1, 1, 0, 1, 1, 0], [0, 1, 1, 0]),
    (![0, 1, 1, 1, 1, 0, 0, 0], [1, 0, 1, 1, 0, 1, 0]),
    (![0, 1, 1, 1, 1, 0, 1, 0], [0, 0, 1, 0, 1, 1, 0, 0]),
    (![0, 1, 1, 1, 1, 1, 0, 0], [1, 0, 0, 1, 0, 1, 0, 0]),
    (![0, 1, 1, 1, 1, 1, 1, 0], [1, 1, 0, 1, 0, 0])]

theorem g2Table_spec : ∀ p ∈ g2Table,
    wordAct p.2 baseVec = p.1 ∨ wordAct p.2 baseVec = p.1 + rVec := by
  decide +kernel

theorem g2Table_cover : ∀ c : Fin 8 → ZMod 2, c 0 + c 7 = 0 → c ≠ 0 → c ≠ rVec →
    ∃ p ∈ g2Table, c = p.1 ∨ c = p.1 + rVec := by
  decide +kernel

theorem vec_sub_add_r : ∀ a : Fin 8 → ZMod 2, a - (a + rVec) = rVec := by decide +kernel

theorem vec_add_r_sub : ∀ a : Fin 8 → ZMod 2, a + rVec - a = rVec := by decide +kernel

theorem wordEvalM_mulVec (w : List (Fin 2)) (v : Fin 8 → ZMod 2) :
    wordEvalM g2M w *ᵥ v = wordAct w v := by
  induction w with
  | nil => simp [wordEvalM, wordAct]
  | cons i w ih =>
    rw [wordEvalM, ← Matrix.mulVec_mulVec, ih]
    rfl

end Coord

section Transport

variable {K : Type} [Field K] (ε : K ≃+* ZMod 2)

@[expose] def coordK (x : quasithinZorn K) : Fin 8 → ZMod 2 := zornCoord (zornMap ε x)

theorem coordK_add (x y : quasithinZorn K) : coordK ε (x + y) = coordK ε x + coordK ε y := by
  rw [coordK, coordK, coordK, zornMap_add, map_add]

theorem coordK_sub (x y : quasithinZorn K) : coordK ε (x - y) = coordK ε x - coordK ε y := by
  have h := coordK_add ε (x - y) y
  rw [sub_add_cancel] at h
  rw [h, add_sub_cancel_right]

theorem coordK_injective : Function.Injective (coordK ε) := by
  intro x y h
  have h' := zornCoord.injective h
  have := congrArg (zornMap ε.symm) h'
  rwa [zornMap_symm_apply, zornMap_symm_apply] at this

theorem coordK_apply (x : quasithinZorn K) :
    coordK ε x = ![ε x.1, ε (x.2.1 0), ε (x.2.1 1), ε (x.2.1 2), ε (x.2.2.1 0), ε (x.2.2.1 1),
      ε (x.2.2.1 2), ε x.2.2.2] := rfl

theorem trace_eq_zero_iff (x : quasithinZorn K) :
    x.1 + x.2.2.2 = 0 ↔ coordK ε x 0 + coordK ε x 7 = 0 := by
  rw [coordK_apply]
  show x.1 + x.2.2.2 = 0 ↔ ε x.1 + ε x.2.2.2 = 0
  rw [← map_add, map_eq_zero_iff ε ε.injective]

theorem coordK_R (c : K) :
    coordK ε ((c, 0, 0, c) : quasithinZorn K) = ![ε c, 0, 0, 0, 0, 0, 0, ε c] := by
  rw [coordK_apply]
  simp

theorem mem_R_iff (x : quasithinZorn K) :
    (∃ c : K, x = (c, 0, 0, c)) ↔ coordK ε x = 0 ∨ coordK ε x = rVec := by
  constructor
  · rintro ⟨c, rfl⟩
    rw [coordK_R]
    have h01 : ∀ t : ZMod 2, t = 0 ∨ t = 1 := by decide
    rcases h01 (ε c) with h | h
    · left
      rw [h]
      funext i
      fin_cases i <;> rfl
    · right
      rw [h]
      rfl
  · rintro (h | h)
    · refine ⟨0, coordK_injective ε ?_⟩
      rw [h, coordK_R, map_zero]
      funext i
      fin_cases i <;> rfl
    · refine ⟨1, coordK_injective ε ?_⟩
      rw [h, coordK_R, map_one]
      rfl

@[expose] noncomputable def gW (w : List (Fin 2)) : quasithinZorn K ≃ₗ[K] quasithinZorn K :=
  (zornConj ε).symm ((wordEval ![g2a, g2b] w : ↥(cayleyGroup (ZMod 2))) :
    quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))

theorem gW_apply (w : List (Fin 2)) (x : quasithinZorn K) :
    gW ε w x = zornMap ε.symm (((wordEval ![g2a, g2b] w : ↥(cayleyGroup (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) (zornMap ε x)) := rfl

theorem coordK_gW
    (w : List (Fin 2)) (x : quasithinZorn K) :
    coordK ε (gW ε w x) = wordAct w (coordK ε x) := by
  rw [coordK, gW_apply, zornMap_apply_symm]
  have h := zornCoord_cg (wordEval ![g2a, g2b] w) (zornMap ε x)
  rw [cmat_wordEval _ _ cmat_ab] at h
  rw [show (cgE (wordEval ![g2a, g2b] w)) (zornMap ε x) = ((wordEval ![g2a, g2b] w :
    ↥(cayleyGroup (ZMod 2))) : quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2))
      (zornMap ε x) from rfl] at h
  rw [h]
  exact wordEvalM_mulVec w _

theorem gW_mem
    [CharP K 2] (w : List (Fin 2)) : gW ε w ∈ ⁅quasithinG2 K, quasithinG2 K⁆ := by
  rw [G11.P3G2.quasithinG2_eq_cayleyGroup]
  have h1 : ((wordEval ![g2a, g2b] w : ↥(cayleyGroup (ZMod 2))) :
      quasithinZorn (ZMod 2) ≃ₗ[ZMod 2] quasithinZorn (ZMod 2)) ∈
        ⁅cayleyGroup (ZMod 2), cayleyGroup (ZMod 2)⁆ := by
    rw [coe_wordEval_sub]
    refine wordEval_mem_of_forall_mem _ _ (fun i => ?_) w
    fin_cases i
    · exact g2a_mem
    · exact g2b_mem
  rw [← map_cayley_commutator ε] at h1
  obtain ⟨γ, hγ, hγe⟩ := h1
  have : gW ε w = γ := by
    rw [gW, ← hγe]
    exact (zornConj ε).symm_apply_apply γ
  rw [this]
  exact hγ

theorem fix_R [CharP K 2] {γ : quasithinZorn K ≃ₗ[K] quasithinZorn K} (hγ : γ ∈ quasithinG2 K)
    (c : K) : γ ((c, 0, 0, c) : quasithinZorn K) = (c, 0, 0, c) := by
  rw [G11.P3G2.quasithinG2_eq_cayleyGroup] at hγ
  have h1 : ((c, 0, 0, c) : quasithinZorn K) = c • cayleyOne K := by
    simp [cayleyOne]
  rw [h1, map_smul, hγ.1]

@[expose] noncomputable def baseK : quasithinZorn K := zornMap ε.symm (zornCoord.symm baseVec)

theorem coordK_baseK : coordK ε (baseK ε) = baseVec := by
  rw [coordK, baseK, zornMap_apply_symm, LinearEquiv.apply_symm_apply]

theorem exists_word
    (x : quasithinZorn K) (hx0 : x.1 + x.2.2.2 = 0)
    (hxR : ¬ ∃ c : K, x = (c, 0, 0, c)) :
    ∃ w : List (Fin 2), ∃ c : K, gW ε w (baseK ε) - x = (c, 0, 0, c) := by
  have h0 := (trace_eq_zero_iff ε x).mp hx0
  have hR := (mem_R_iff ε x).not.mp hxR
  push Not at hR
  obtain ⟨p, hp, hpc⟩ := g2Table_cover (coordK ε x) h0 hR.1 hR.2
  refine ⟨p.2, (mem_R_iff ε _).mpr ?_⟩
  rw [coordK_sub, coordK_gW, coordK_baseK]
  rcases g2Table_spec p hp with h | h <;> rcases hpc with e | e <;> rw [h, e]
  · left
    exact sub_self _
  · right
    exact vec_sub_add_r _
  · right
    exact vec_add_r_sub _
  · left
    exact sub_self _

end Transport

theorem zornQ_transitive
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    ∀ m₁ ∈ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      m₁ ∉ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).ker →
    ∀ m₂ ∈ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).sec,
      m₂ ∉ (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).ker →
      ∃ γ : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam,
        (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).act γ m₁ * m₂⁻¹ ∈
          (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).ker := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := 1) (by rw [hF, pow_one])
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  intro (m₁ : Multiplicative (quasithinZorn K)) hm₁ hk₁ (m₂ : Multiplicative (quasithinZorn K)) hm₂
    hk₂
  obtain ⟨w₁, c₁, hc₁⟩ := exists_word ε (Multiplicative.toAdd m₁) hm₁ hk₁
  obtain ⟨w₂, c₂, hc₂⟩ := exists_word ε (Multiplicative.toAdd m₂) hm₂ hk₂
  have hle : ⁅quasithinG2 K, quasithinG2 K⁆ ≤ quasithinG2 K := B5.commutator_le_self _
  let g₁ : ↥⁅quasithinG2 K, quasithinG2 K⁆ := ⟨gW ε w₁, gW_mem ε w₁⟩
  let g₂ : ↥⁅quasithinG2 K, quasithinG2 K⁆ := ⟨gW ε w₂, gW_mem ε w₂⟩
  refine ⟨g₂ * g₁⁻¹, ?_⟩
  have hg1i : ((g₁⁻¹ : ↥⁅quasithinG2 K, quasithinG2 K⁆) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
      quasithinG2 K := hle (g₁⁻¹).2
  have hg2 : ((g₂ : ↥⁅quasithinG2 K, quasithinG2 K⁆) : quasithinZorn K ≃ₗ[K] quasithinZorn K) ∈
      quasithinG2 K := hle g₂.2
  have hinv : ((g₁⁻¹ : ↥⁅quasithinG2 K, quasithinG2 K⁆) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (Multiplicative.toAdd m₁) = baseK ε - (c₁, 0, 0, c₁) := by
    have e1 : Multiplicative.toAdd m₁ = gW ε w₁ (baseK ε) - (c₁, 0, 0, c₁) := by
      rw [← hc₁, sub_sub_cancel]
    have e2 : ((g₁⁻¹ : ↥⁅quasithinG2 K, quasithinG2 K⁆) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (gW ε w₁ (baseK ε)) = baseK ε := by
      show (gW ε w₁)⁻¹ (gW ε w₁ (baseK ε)) = baseK ε
      exact (gW ε w₁).symm_apply_apply (baseK ε)
    rw [e1, map_sub, e2, fix_R hg1i]
  refine ⟨c₂ - c₁, ?_⟩
  show Multiplicative.toAdd (Multiplicative.ofAdd
      (((g₂ * g₁⁻¹ : ↥⁅quasithinG2 K, quasithinG2 K⁆) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (Multiplicative.toAdd m₁)) * m₂⁻¹) = _
  rw [toAdd_mul, toAdd_ofAdd, toAdd_inv]
  show (g₂ : quasithinZorn K ≃ₗ[K] quasithinZorn K)
      (((g₁⁻¹ : ↥⁅quasithinG2 K, quasithinG2 K⁆) : quasithinZorn K ≃ₗ[K] quasithinZorn K)
        (Multiplicative.toAdd m₁)) + -Multiplicative.toAdd m₂ = _
  rw [hinv, map_sub, fix_R hg2]
  have e3 : (g₂ : quasithinZorn K ≃ₗ[K] quasithinZorn K) (baseK ε) =
      Multiplicative.toAdd m₂ + (c₂, 0, 0, c₂) := by
    rw [← hc₂, add_sub_cancel]
  rw [e3]
  ext <;> simp <;> ring

theorem coord5_ne : ∀ k l : Fin 5, k ≠ l →
    (Pi.single (⟨k.val + 1, by omega⟩ : Fin 8) (1 : ZMod 2) -
        Pi.single (⟨l.val + 1, by omega⟩ : Fin 8) 1 : Fin 8 → ZMod 2) ≠ 0 ∧
      (Pi.single (⟨k.val + 1, by omega⟩ : Fin 8) (1 : ZMod 2) -
        Pi.single (⟨l.val + 1, by omega⟩ : Fin 8) 1 : Fin 8 → ZMod 2) ≠ rVec := by
  decide +kernel

theorem coord5_trace : ∀ k : Fin 5,
    (Pi.single (⟨k.val + 1, by omega⟩ : Fin 8) (1 : ZMod 2) : Fin 8 → ZMod 2) 0 +
      (Pi.single (⟨k.val + 1, by omega⟩ : Fin 8) (1 : ZMod 2) : Fin 8 → ZMod 2) 7 = 0 := by
  decide +kernel

theorem four_lt_card_zornQ {V : Type} [CommGroup V] [Finite V] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) {H : Subgroup (MulAut V)}
    {π : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Gam →* ↥H}
    (h : (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).RealizesVia H ⊤ ⊥ π) : 4 < Nat.card V := by
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hK]
  let ε : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  obtain ⟨e, -⟩ := G64.RealizesVia.exists_modEquiv h
  have : Finite (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Mod := Finite.of_equiv V e.toEquiv
  rw [Nat.card_congr e.toEquiv]
  let xk : Fin 5 → quasithinZorn K := fun k =>
    zornMap ε.symm (zornCoord.symm (Pi.single (⟨k.val + 1, by omega⟩ : Fin 8) 1))
  have hxk : ∀ k, coordK ε (xk k) = Pi.single (⟨k.val + 1, by omega⟩ : Fin 8) 1 := fun k => by
    rw [coordK, zornMap_apply_symm, LinearEquiv.apply_symm_apply]
  have hmem : ∀ k, Multiplicative.ofAdd (xk k) ∈ zornO0 K := fun k => by
    show (xk k).1 + (xk k).2.2.2 = 0
    rw [trace_eq_zero_iff ε, hxk]
    exact coord5_trace k
  let f : Fin 5 → (FFModel.zornQ ⁅quasithinG2 K, quasithinG2 K⁆).Mod :=
    fun k => QuotientGroup.mk ⟨Multiplicative.ofAdd (xk k), hmem k⟩
  have hf : Function.Injective f := by
    intro k l hkl
    by_contra hne
    have h1 := QuotientGroup.eq.mp hkl
    rw [Subgroup.mem_subgroupOf] at h1
    obtain ⟨c, hc⟩ := h1
    have h2 : coordK ε (xk l - xk k) = 0 ∨ coordK ε (xk l - xk k) = rVec := by
      refine (mem_R_iff ε _).mp ⟨c, ?_⟩
      rw [← hc]
      show xk l - xk k = Multiplicative.toAdd ((Multiplicative.ofAdd (xk k))⁻¹ *
        Multiplicative.ofAdd (xk l))
      rw [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_ofAdd, neg_add_eq_sub]
    rw [coordK_sub, hxk, hxk] at h2
    obtain ⟨h3, h4⟩ := coord5_ne l k (Ne.symm hne)
    rcases h2 with h2 | h2
    · exact h3 h2
    · exact h4 h2
  have := Nat.card_le_card_of_injective f hf
  rw [Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin] at this
  omega

theorem quad_rows_G2
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ w : V, w ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hB4 : B4Hyp G L)
    (hrow : G2Natural (ffJ G) ⊤ ⊥ 1 ∨ G2NaturalDerived L ⊤ ⊥ 1)
    (q : V → ZMod 2) (hq : ∀ x ∈ G, ∀ w, q (x w) = q w)
    (hβ : ∀ a b w, polarQ q (a * b) w = polarQ q a w + polarQ q b w)
    (hnd : ∀ a, a ≠ 1 → ∃ w, polarQ q a w ≠ 0) : False := by
  obtain ⟨X, hXG, hX⟩ : ∃ X ≤ G, G2NaturalDerived X ⊤ ⊥ 1 := by
    rcases hrow with h | h
    · exact ⟨⁅ffJ G, ffJ G⁆, (B5.commutator_le_self _).trans (B6.ffJ_le G),
        B5.g2NaturalDerived_of_g2Natural h⟩
    · exact ⟨L, hB4.2.1 ▸ quasithinGenFitting_le G, h⟩
  obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := hX
  rw [pow_one] at hKc
  exact false_of_transitive_quad hV X (transitive_of_realizesVia hπ (zornQ_transitive hKc))
    (four_lt_card_zornQ hKc hπ) q (fun x hx => hq x (hXG hx)) hβ hnd

theorem factQuadRows1321 :
    FactQuadRows1321 := by
  intro V _ _ hV G L A hB4 hrow v _ _ c hc _ hc3 _ q hq hβ hnd
  rcases hrow with h6 | hSp | h10 | hG2 | hG2'
  · exact (quad_rows_A6 hV hB4 (Or.inl h6) q hq hβ hnd).elim
  · exact (quad_rows_A6 (A := A) hV hB4 (Or.inr hSp) q hq hβ hnd).elim
  · obtain ⟨π, hπ⟩ := alternatingNatural_eight_of_extSq h10.1
    have hLG : L ≤ G := hB4.2.1 ▸ quasithinGenFitting_le G
    exact quad_row_A8 hπ hV q (fun x hx => hq x (hLG hx)) hβ hnd hc hc3
  · exact (quad_rows_G2 hV hB4 (Or.inl hG2) q hq hβ hnd).elim
  · exact (quad_rows_G2 hV hB4 (Or.inr hG2') q hq hβ hnd).elim

end CFSG.Quasithin.H13.A5
