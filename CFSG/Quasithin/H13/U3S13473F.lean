module

public import CFSG.Quasithin.H13.U3S13473N
public import CFSG.Quasithin.H13.U3S13473C
public import CFSG.Quasithin.H13.U3S13473D
public import CFSG.Quasithin.H13.U3S1347P4A

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

structure Data13473 (S : A6.Setting134 G T L V) (H₁ H₂ Y₂ Y : Subgroup G) : Prop where
  he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))
  inH₀ : InH T (H₁ ⊔ H₂)
  notM₀ : ¬ H₁ ⊔ H₂ ≤ normalizer (L : Set G)
  J₀ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G)
  le : Y₂ ≤ H₁ ⊔ H₂
  normal : H₁ ⊔ H₂ ≤ normalizer (Y₂ : Set G)
  res : oTwoRes Y₂ = Y₂
  fpf : ∀ y ∈ Y₂, y ∉ centralizer (v0Of T H₁ H₂ : Set G) →
    ∀ w ∈ v0Of T H₁ H₂, y * w * y⁻¹ = w → w = 1
  moves : ∃ y ∈ Y₂, y ∉ centralizer (v0Of T H₁ H₂ : Set G)
  Z_le : quasithinOmegaOneCenter T ≤ v0Of T H₁ H₂
  inf_le : Y₂ ⊓ T ≤ centralizer (v0Of T H₁ H₂ : Set G)
  index : T.relIndex (Y₂ ⊔ T) = 3
  s3 : quasithinO2QuotientIso (Y₂ ⊔ T) (Perm (Fin 3))
  notM : ¬ Y₂ ≤ normalizer (L : Set G)
  cyc : pCoreOf 2 Y₂ = ⊥ → IsCyclic ↥Y₂
  hY : Y = (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T)
  inf : (L₁Of L (fsuV1 T V) ⊔ T) ⊓ (Y₂ ⊔ T) = T
  triple : F6.IsGoldschmidtTripleIn Y (L₁Of L (fsuV1 T V) ⊔ T) (Y₂ ⊔ T)
  inH : InH T Y
  notMY : ¬ Y ≤ normalizer (L : Set G)
  red : IsTwoReducedIn Y (VZ T Y)
  cent : Y ⊓ centralizer (VZ T Y : Set G) = pCoreOf 2 Y
  commJ : ⁅L₁Of L (fsuV1 T V), thompsonJ T⁆ = L₁Of L (fsuV1 T V)
  notJ : ¬ thompsonJ T ≤ pCoreOf 2 Y
  ne : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≠ pCoreOf 2 (Y₂ ⊔ T)
  notComm : ∀ Q : Subgroup G, IsPGroup 2 ↥Q → Q ≤ T →
    L₁Of L (fsuV1 T V) ≤ normalizer (Q : Set G) →
      ¬ ∀ y ∈ Y₂, ∀ l ∈ L₁Of L (fsuV1 T V), y * l * y⁻¹ * l⁻¹ ∈ Q

theorem exists_data13473 (hedge : GoldschmidtEdgeBoundS3)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (h135 : A6.Stmt13_3_5) (h1222 : Stmt12_2_2) (h139 : A6.Stmt13_3_9)
    (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G} (h : Hyp1347 T H₁ H₂)
    (hK₂L : oTwoRes H₂ = l2Of S) (hiii : Concl1347iii T H₁ H₂) :
    ∃ Y₂ Y : Subgroup G, Data13473 S H₁ H₂ Y₂ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have he := s1347_a6_of_K2 h1332 S h hK₂L
  obtain ⟨hH₀, hH₀M, -⟩ := s1347_one_first hedge h1332 h1228 hC58 h317 h56 h135 S h
  have hJ : H₁ ⊔ H₂ ≤ normalizer (thompsonJ T : Set G) := hiii.2.2.2
  obtain ⟨Y₂, hY₂H, hY₂N, hY₂, hfpf, hmoves, hY₂T, h3, hq, hY₂M⟩ :=
    s1347_iii_Y2 hedge h1332 h1228 hC58 h317 h56 h135 h1222 S h hiii
  have hTN : T ≤ normalizer (Y₂ : Set G) := hH₀.1.trans hY₂N
  have hcyc := s1347_iii_cyclic S hH₀ hiii hY₂H hY₂T h3 hTN
  obtain ⟨hinf, htr, hY, hYM⟩ := s1347_Y_triple hedge S he h3 hq hY₂M
  have hnot : ∀ Q : Subgroup G, IsPGroup 2 ↥Q → Q ≤ T →
      L₁Of L (fsuV1 T V) ≤ normalizer (Q : Set G) →
        ¬ ∀ y ∈ Y₂, ∀ l ∈ L₁Of L (fsuV1 T V), y * l * y⁻¹ * l⁻¹ ∈ Q := fun Q hQ2 hQT hL₁Q =>
    s1347_not_comm_of S he hK₂L hH₀.1 hY₂ hY₂N hY₂M hcyc hQ2 hQT hL₁Q
  have hnc := hnot (pCoreOf 2 (L₁Of L (fsuV1 T V))) (pCoreOf_isPGroup 2 _)
    ((s134_L1T_a6 S he).2.1 ▸ inf_le_right) (le_normalizer_pCoreOf 2 _)
  obtain ⟨hred, hcent⟩ := s1347_Y_cent h139 S he hY hYM (le_sup_left.trans le_sup_right) hY₂ hnc
  have hJR := s1347_thompsonJ_not_le_R S he hK₂L hH₀M hJ hH₀.1 hY₂H
  exact ⟨Y₂, _, he, hH₀, hH₀M, hJ, hY₂H, hY₂N, hY₂, hfpf, hmoves, s1347_Z_le_V0, hY₂T, h3, hq,
    hY₂M, hcyc, rfl, hinf, htr, hY, hYM, hred, hcent, s134_comm_thompsonJ_L1 S he hJR,
    s1347_thompsonJ_not_le_pCoreOf S he hK₂L hH₀M hJ (le_sup_right.trans le_sup_left)
      (le_sup_left.trans le_sup_left),
    s1347_iii_pCoreOf_ne S he hK₂L hH₀M hJ hH₀.1 hY₂H, hnot⟩

theorem Data13473.isSolvable (hns : Stmt13473NonSolv) {S : A6.Setting134 G T L V}
    {H₁ H₂ Y₂ Y : Subgroup G} (h : Hyp1347 T H₁ H₂) (hK₂L : oTwoRes H₂ = l2Of S)
    (hiii : Concl1347iii T H₁ H₂) (D : Data13473 S H₁ H₂ Y₂ Y) : Group.IsSolvable ↥Y := by
  by_contra hns'
  exact hns G T L V S H₁ H₂ Y₂ Y D.he h hK₂L hiii D.inH₀ D.notM₀ D.le D.normal D.res D.fpf
    D.moves D.Z_le D.inf_le D.index D.s3 D.notM D.hY D.inf D.triple D.inH D.notMY D.red D.cent
    D.commJ D.notJ D.notComm hns'

end CFSG.Quasithin.H13.U3
