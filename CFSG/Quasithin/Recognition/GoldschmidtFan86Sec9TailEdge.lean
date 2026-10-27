module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Tail
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9Ex
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P5Card
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F87C
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3F92Card
public import CFSG.Certificates.Kernel.LocalCompTits.Span
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporSimpleTop
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
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
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Background.F6Solvable
public import CFSG.Quasithin.Background.F9G2
public import CFSG.Quasithin.Background.F9Geometry
public import CFSG.Quasithin.Background.F9Tilde
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocCheck
public import CFSG.Quasithin.EmptyFaithful.S1417Sylow
public import CFSG.Quasithin.EmptyFaithful.S1421Final
public import CFSG.Quasithin.EmptyFaithful.S1421L246
public import CFSG.Quasithin.EmptyFaithful.S143Pre
public import CFSG.Quasithin.EmptyFaithful.S145Basic
public import CFSG.Quasithin.EmptyFaithful.S146Defs
public import CFSG.Quasithin.EmptyFaithful.S146S3
public import CFSG.Quasithin.Recognition.F112TitsB2
public import CFSG.Quasithin.Recognition.F112TitsFrob
public import CFSG.Quasithin.Recognition.F112TitsMain3
public import CFSG.Quasithin.Recognition.F112WAssembly
public import CFSG.Quasithin.Recognition.F112WLocal2
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Assembly
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TreeMain
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import Certificates.Data.CFSGNative.MonsterB.Rep4371Model
public import Certificates.Kernel.J4Count.FixCE
public import Certificates.Kernel.J4Count.FixCPairBase1
public import Certificates.Kernel.J4Count.KFactsBase

public section

namespace CFSG.Quasithin.Fan86

open CFSG.Quasithin

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace D10Set

variable {L : ZLab Γ G} {α : V}

theorem card_calpha_of_fan84a {F : FanTree Γ G} (h7 : Fan7 F L) (h84 : Fan84a F L)
    (D : D10Set L α) : Nat.card D.calpha = 2 ∨ Nat.card D.calpha = 4 := by
  obtain ⟨-, hle⟩ := h84 α D
  have := F87.finite_calpha F D
  have hz := F87.z_mem_calpha h7 D
  have hzz : (⟨L.z α, hz⟩ : ↥D.calpha) ^ 2 = 1 :=
    Subtype.ext (by simpa [pow_two] using L.z_mul_self D.val)
  have hz1 : (⟨L.z α, hz⟩ : ↥D.calpha) ≠ 1 := fun h => L.z_ne_one D.val (congrArg Subtype.val h)
  have hzo : orderOf (⟨L.z α, hz⟩ : ↥D.calpha) = 2 := orderOf_eq_prime hzz hz1
  have h2 : 2 ∣ Nat.card ↥D.calpha := hzo ▸ orderOf_dvd_natCard _
  have hpos : 0 < Nat.card ↥D.calpha := Nat.card_pos
  omega

end D10Set

theorem tail_edge (F : FanTree Γ G) (L : ZLab Γ G) (h7 : Fan7 F L) (h65 : Fan65 F)
    (h84 : Fan84a F L) (hex : SecCfgExists F L) (h915 : Fan915 F L) {α β : V}
    (hαβ : Γ.Adj α β) (hα : valence Γ α = 5) :
    ∃ n : ℕ, (n = 11 ∨ n = 12) ∧
      Nat.card ↥(MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 2 ^ n ∧
      AdmitsPres n (GoldAmalgam.ofSubgroupPair (MulAction.stabilizer G α)
        (MulAction.stabilizer G β)) := by
  obtain ⟨S, rfl, rfl, hStar⟩ := hex α β hα hαβ
  have hfive := F.card_stabilizer_eq_five_mul hα hαβ
  have hS := F.card_stabilizer_eq h65 h7.2.2.1 S.D
  have h := h915 S hStar
  rcases S.D.card_calpha_of_fan84a h7 h84 with hC | hC
  · rw [hC] at hS
    have hE : Nat.card ↥(MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta) = 2 ^ 11 := by
      omega
    exact ⟨11, Or.inl rfl, hE, h.1 hE⟩
  · rw [hC] at hS
    have hE : Nat.card ↥(MulAction.stabilizer G S.α ⊓ MulAction.stabilizer G S.beta) = 2 ^ 12 := by
      omega
    exact ⟨12, Or.inr rfl, hE, h.2 hE⟩

theorem fanTail_of_items
    (h84 : ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V) (F : FanTree Γ G)
      (L : ZLab Γ G), Fan7 F L → Fan65 F → Fan66 F → Fan517 F L → Fan512 F L → Fan84a F L)
    (hex : ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V) (F : FanTree Γ G)
      (L : ZLab Γ G), Fan7 F L → Fan65 F → Fan66 F → Fan517 F L → Fan512 F L →
        SecCfgExists F L)
    (h915 : ∀ (V G : Type) [Group G] [MulAction G V] (Γ : SimpleGraph V) (F : FanTree Γ G)
      (L : ZLab Γ G), Fan7 F L → Fan65 F → Fan66 F → Fan517 F L → Fan512 F L → Fan915 F L) :
    FanTail := fun V G _ _ Γ F L h7 h65 h66 h517 h512 _ _ hαβ hα =>
  tail_edge F L h7 h65 (h84 V G Γ F L h7 h65 h66 h517 h512) (hex V G Γ F L h7 h65 h66 h517 h512)
    (h915 V G Γ F L h7 h65 h66 h517 h512) hαβ hα

end CFSG.Quasithin.Fan86
