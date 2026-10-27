module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.HeParabolicsHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.He2CaseBTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.He2CaseBSeven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.E2P CFSG.Quasithin.E2P.SporB CFSG.Quasithin.ModH CFSG.Quasithin.ModH.He2
open CFSG.Quasithin.RonanE114.HeOver CFSG.QuasithinUnique
open CFSG.QuasithinUnique.Ch1.SporLat.He (heIncl)
open CFSG.LocalAnalysis.WeakClosure81
open scoped Pointwise commutatorElement

theorem he2_outerParabolics_of_lat
    {Γ : Type} [Group Γ] [Finite Γ] (hl : HeLat Γ)
    {Y : Type} [Group Y] [Finite Y] {K S : Subgroup Y} [K.Normal] (e : ↥K ≃* Γ)
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S ⊤) (hSKtop : S ⊔ K = ⊤)
    (h128 : Nat.card (CFSG.pCore 2 ↥(hl.Y 7)) = 128) :
    ∃ H₁ H₂ H₃ : Subgroup Y, S ≤ H₁ ∧ S ≤ H₂ ∧ S ≤ H₃ ∧
      CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₁ ∧
        CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₂ ∧
          CFSG.LocalAnalysis.WeakClosure81.InFSq 1 H₃ ∧
            H₁ ⊔ H₂ ⊔ H₃ = ⊤ := by
  have hSK : CFSG.QuasithinUnique.IsSylowTwoOf (S ⊓ K) K :=
    CFSG.Quasithin.B6.isSylowTwoOf_inf_normal hS le_top fun x _ => by
      rw [Subgroup.normalizer_eq_top_iff.mpr ‹K.Normal›]; trivial
  obtain ⟨e', he'⟩ := CFSG.Quasithin.E2P.SporB.exists_equiv_sylow e hSK hl.S_sylow
  by_cases hA : ∀ t ∈ S, (hl.Y 3).map (autK e' t).toMonoidHom = hl.Y 3
  · exact he2_caseA hl e' he' hS hSKtop hA
  · push Not at hA
    obtain ⟨s, hsS, hne⟩ := hA
    have hα : ∀ t ∈ S, hl.S.map (autK e' t).toMonoidHom = hl.S :=
      he2_map_S_of_mem hl e' he'
    have hswap : (hl.Y 3).map (autK e' s).toMonoidHom = hl.Y 4 :=
      ((aut_Y34 hl (hα s hsS)).resolve_left fun h => hne h.1).1
    have hP7 : InFSq 1 (S ⊔ ((hl.Y 7).map e'.symm.toMonoidHom).map K.subtype) :=
      he2_caseB_seven hl e' he' hS hsS hswap h128
    have hP2 : InFSq 1 (S ⊔ ((hl.Y 2).map e'.symm.toMonoidHom).map K.subtype) :=
      he2_caseB_two hl e' he' hS hsS hswap
    have hgen27 : hl.Y 2 ⊔ hl.Y 7 = ⊤ := by
      have hSle : hl.S ≤ hl.Y 2 ⊔ hl.Y 7 := le_sup_of_le_left (hl.S_le_Y 2)
      rcases hl.complete _ hSle with ⟨j, hj, hjeq⟩ | htop
      · exfalso
        have h2j : hl.Y 2 ≤ hl.Y j := hjeq ▸ le_sup_left
        have h7j : hl.Y 7 ≤ hl.Y j := hjeq ▸ le_sup_right
        have key : ∀ j < 11, j ∈ heIncl[2]! → j ∈ heIncl[7]! → False := by decide
        exact key j hj ((hl.le_iff (by norm_num) hj).mp h2j)
          ((hl.le_iff (by norm_num) hj).mp h7j)
      · exact htop
    have hpull : ((hl.Y 7).map e'.symm.toMonoidHom).map K.subtype ⊔
        ((hl.Y 2).map e'.symm.toMonoidHom).map K.subtype = K := by
      rw [← pull_sup, sup_comm (hl.Y 7) (hl.Y 2), hgen27, pull_top]
    refine ⟨S ⊔ ((hl.Y 7).map e'.symm.toMonoidHom).map K.subtype,
      S ⊔ ((hl.Y 2).map e'.symm.toMonoidHom).map K.subtype,
      S ⊔ ((hl.Y 7).map e'.symm.toMonoidHom).map K.subtype,
      le_sup_left, le_sup_left, le_sup_left, hP7, hP2, hP7, ?_⟩
    calc (S ⊔ ((hl.Y 7).map e'.symm.toMonoidHom).map K.subtype) ⊔
          (S ⊔ ((hl.Y 2).map e'.symm.toMonoidHom).map K.subtype) ⊔
          (S ⊔ ((hl.Y 7).map e'.symm.toMonoidHom).map K.subtype)
        = S ⊔ (((hl.Y 7).map e'.symm.toMonoidHom).map K.subtype ⊔
            ((hl.Y 2).map e'.symm.toMonoidHom).map K.subtype) := by ac_rfl
      _ = S ⊔ K := by rw [hpull]
      _ = ⊤ := hSKtop

theorem k_HeOuterParabolics_holds :
    K_HeOuterParabolics := by
  intro Y _ _ K hKN hq hodd hHe hKtop hcent hidx S hS
  obtain ⟨e₀⟩ := hHe
  have : K.Normal := hKN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSKtop : S ⊔ K = ⊤ := by
    have hSidx : ¬ 2 ∣ S.index := by
      simpa [Subgroup.relIndex_top_right] using hS.2.2
    let Ss : Sylow 2 Y := hS.2.1.toSylow hSidx
    have hSs : (Ss : Subgroup Y) = S := IsPGroup.toSylow_coe hS.2.1 hSidx
    have h := CFSG.QuasiDihedralFusion.normal_sup_sylow_eq_top K hidx Ss
    rwa [hSs, sup_comm] at h
  exact he2_outerParabolics_of_lat CFSG.Quasithin.RonanE114.HeOver.heLatNative
    (e₀.trans CFSG.Sporadic.He.heEquivJ) hS hSKtop
    CFSG.Quasithin.RonanE114.HeOver.he_card_pCore_Y7

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
