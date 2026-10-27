module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P65Core
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P65Sz
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P63
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P64
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8Hyp
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PXiLoc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T P62 P63

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P65

theorem exists_cinv_five (F : FanTree Γ G) (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T)
    (h61 : Fan61 F) (h62 : Fan62 F) (h512cen : Fan512cen F) :
    ∃ (α : V) (z : G), valence Γ α = 5 ∧ z ∈ Cinv G α := by
  obtain ⟨T, hT⟩ := hΞ
  have hadj : Γ.Adj (T.line.vert 0) (T.line.vert (0 + 1)) := T.line.adj 0
  have hE2 : IsPGroup 2 ↥(MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert (0 + 1))) := F.edge_two _ _ hadj
  have hEfin : Finite ↥(MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert (0 + 1))) := F.finite_stabilizer_inf _ _
  have hEnt : Nontrivial ↥(MulAction.stabilizer G (T.line.vert 0) ⊓
      MulAction.stabilizer G (T.line.vert (0 + 1))) := by
    obtain ⟨k, hk⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 (F.nbrStab_ne_bot h40 (T.line.vert 0))
    refine nontrivial_of_ne ⟨(k : G), F.nbrStab_le_edge _ hadj k.2⟩ 1 fun h => hk (Subtype.ext ?_)
    simpa using congrArg Subtype.val h
  obtain ⟨z, hzE, hz1, hzz, hzc⟩ := exists_central_involution_of_isPGroup hE2
  have hzZ : z ∈ T.line.ZZ := ⟨hzz, 0, hzE, hzc⟩
  obtain ⟨⟨a, b, tL, tR, hcf⟩, hP⟩ := h62 h40 T hT z hzZ hz1
  have hb : b = a + 2 := by have := (hP a b tL tR hcf).1; omega
  have hcore : T.line.IsCore z a (a + 2) := hb ▸ hcf.core
  have hcin := h512cen h40 T z a hT hzZ hz1 hcore
  have hne := h61 h40 _ z hcin
  have h35 : valence Γ (T.line.vert (a + 1)) = 3 ∨ valence Γ (T.line.vert (a + 1)) = 5 :=
    F.valence _
  exact ⟨T.line.vert (a + 1), z, by omega, hcin⟩

end P65

theorem fan65 (F : FanTree Γ G) (h40 : Fan40 F) (hΞ : ∃ T : Track Γ G, InXi T) (h61 : Fan61 F)
    (h62 : Fan62 F) (h512b : Fan512b F) (h512cen : Fan512cen F) (h517a : Fan517a F)
    (hD : LemmaD F) (h517c : Fan517c F) (h33 : Fan33 F) : Fan65 F := by
  have h63 := fan63 F hΞ h61 h62 h512b h517a hD h517c
  have h64 := fan64 F hΞ h61 h62 h512b h517a hD h517c
  obtain ⟨α₀, z₀, hα₀, hz₀⟩ := P65.exists_cinv_five F h40 hΞ h61 h62 h512cen
  obtain ⟨L, ℓ, j, -, -, D⟩ := exists_lab_data F h40 hΞ h62 h512b h517a hD h517c hα₀ hz₀
  refine ⟨fun α hα x hx hxo => (P65.core_at F h40 h33 h63 h64 h517a D hα).1 x hx hxo,
    fun α hα => ?_⟩
  obtain ⟨β, hαβ⟩ := F.exists_adj α
  exact P65.nonempty_oTwoQuot_sz F hα hαβ ((P65.core_at F h40 h33 h63 h64 h517a D hα).2 β hαβ)

end CFSG.Quasithin.Fan86
