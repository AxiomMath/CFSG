module

public import CFSG.Quasithin.H13.U3S13473E
public import CFSG.Quasithin.H13.U3S13473G
public import CFSG.Quasithin.H13.U3S13473F

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem Data13473.not_isSolvable (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big)
    {S : A6.Setting134 G T L V} {H₁ H₂ Y₂ Y : Subgroup G}
    (hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4) (D : Data13473 S H₁ H₂ Y₂ Y) :
    ¬ Group.IsSolvable ↥Y := by
  intro hsolv
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hq₁ := (s134_L1T_a6 S D.he).2.2
  have hY := D.hY
  subst hY
  obtain ⟨hcase, hT4⟩ := solv_f618_of_triple hF hBig S D.triple D.inf hq₁ D.s3 D.inH hsolv D.ne
  have hN := pPrimeCore_eq_of_triple S D.triple D.inf D.inH hsolv D.ne hT4
  have hOT : pCoreOf 2 ((L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T)) ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow D.inH.1)
  rcases hcase with ⟨⟨e⟩⟩ | hext
  ·
    have hc := comm_le_of_s3s3 hN e
    have hL₁ : L₁Of L (fsuV1 T V) ≤ oTwoRes (L₁Of L (fsuV1 T V) ⊔ T) :=
      calc L₁Of L (fsuV1 T V) = oTwoRes (L₁Of L (fsuV1 T V)) := (S14.oTwoRes_idem _).symm
        _ ≤ oTwoRes (L₁Of L (fsuV1 T V) ⊔ T) := oTwoRes_mono' le_sup_left
    have hY₂ : Y₂ ≤ oTwoRes (Y₂ ⊔ T) :=
      calc Y₂ = oTwoRes Y₂ := D.res.symm
        _ ≤ oTwoRes (Y₂ ⊔ T) := oTwoRes_mono' le_sup_left
    apply D.notComm _ (pCoreOf_isPGroup 2 _) hOT
      ((le_sup_left.trans le_sup_left).trans (le_normalizer_pCoreOf 2 _))
    intro y hy l hl
    have h1 : ⁅y, l⁆ ∈ ⁅oTwoRes (L₁Of L (fsuV1 T V) ⊔ T), oTwoRes (Y₂ ⊔ T)⁆ := by
      rw [commutator_comm]
      exact commutator_mem_commutator (hY₂ hy) (hL₁ hl)
    have h2 := hc h1
    rwa [commutatorElement_def] at h2
  ·
    apply D.notJ
    have hVe := D.red.2.2.1
    have hV2 : IsPGroup 2 ↥(VZ T ((L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T))) := fun w =>
      ⟨1, Subtype.ext (by simpa using hVe.2 w w.2)⟩
    have hVT : VZ T ((L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T)) ≤ T :=
      (le_pCoreOf_of_le_normalizer 2 D.red.1 D.red.2.1 hV2).trans hOT
    exact thompsonJ_le_of_E4 S D.inH.1 D.red hVT D.cent hZ4 hT4 (isExtensionWith_of_eq hN hext)

theorem s1347_three (hns : Stmt13473NonSolv)
    (hF : F6.TheoremF618Cat) (hBig : A5.FactF618Big) (hedge : GoldschmidtEdgeBoundS3)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h135 : A6.Stmt13_3_5) (h1222 : Stmt12_2_2) (h139 : A6.Stmt13_3_9)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂L : oTwoRes H₂ = l2Of S) : ¬ Concl1347iii T H₁ H₂ := by
  intro hiii
  obtain ⟨Y₂, Y, D⟩ :=
    exists_data13473 hedge h1332 h1228 hC58 h317 h56 h135 h1222 h139 S h hK₂L hiii
  obtain ⟨-, -, -, -, -, hc₁, -⟩ := s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hZ4 : Nat.card ↥(quasithinOmegaOneCenter T) = 4 := by rw [h.index₁, hc₁]
  exact D.not_isSolvable hF hBig hZ4 (D.isSolvable hns h hK₂L hiii)

end CFSG.Quasithin.H13.U3
