module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86ModelFrob
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc2

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P65

variable (F : FanTree Γ G)
include F

theorem nbrStab_le_pCore (v : V) :
    (nbrStab Γ G v).subgroupOf (MulAction.stabilizer G v) ≤
      Open.pCore 2 ↥(MulAction.stabilizer G v) := by
  have hnorm : ((nbrStab Γ G v).subgroupOf (MulAction.stabilizer G v)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer (F.nbrStab_le_stabilizer v)]
    intro g hg
    have hg' : g • v = v := MulAction.mem_stabilizer_iff.1 hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => nbrStab_conj_mem F hg' hh, fun hh => ?_⟩
    have := nbrStab_conj_mem F (g := g⁻¹) (by rw [inv_smul_eq_iff]; exact hg'.symm) hh
    simpa [mul_assoc] using this
  have hp : IsPGroup 2 ↥((nbrStab Γ G v).subgroupOf (MulAction.stabilizer G v)) :=
    (F.nbrStab_isPGroup v).of_equiv (Subgroup.subgroupOfEquivOfLe (F.nbrStab_le_stabilizer v)).symm
  exact le_pCore 2 hnorm hp

theorem pCore_le_nbrStab (v : V) :
    Open.pCore 2 ↥(MulAction.stabilizer G v) ≤
      (nbrStab Γ G v).subgroupOf (MulAction.stabilizer G v) := by
  set H := MulAction.stabilizer G v with hH
  intro x hx
  have : Finite H := F.loc_finite v
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 (pCoreOf 2 H) :=
    (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥H) 2).map H.subtype
  have hxP : (x : G) ∈ pCoreOf 2 H := ⟨x, hx, rfl⟩
  obtain ⟨w, hw, hwfix⟩ := F.exists_fixed_nbr_of_two_group v (pCoreOf 2 H) (pCoreOf_le 2 H)
    (fun g hg => by
      obtain ⟨k, hk⟩ := hO2 ⟨g, hg⟩
      refine ⟨k, ?_⟩
      have : g ^ 2 ^ k = 1 := congrArg Subtype.val hk
      rw [this]
      exact (nbrStab Γ G v).one_mem)
  rw [Subgroup.mem_subgroupOf]
  refine mem_nbrStab.2 fun u hu => ?_
  obtain ⟨s, hs, hsw⟩ := F.loc_trans v w u hw hu
  have hn := le_normalizer_pCoreOf 2 H (H.inv_mem hs)
  have h1 : s⁻¹ * (x : G) * s⁻¹⁻¹ ∈ pCoreOf 2 H := (Subgroup.mem_normalizer_iff.1 hn _).1 hxP
  have h2 := hwfix _ h1
  rw [← hsw, ← mul_smul]
  calc ((x : G) * s) • w = s • ((s⁻¹ * (x : G) * s⁻¹⁻¹) • w) := by
        rw [← mul_smul]
        congr 1
        group
    _ = s • w := by rw [h2]

theorem nonempty_oTwoQuot_sz {α β : V} (hv5 : valence Γ α = 5) (hαβ : Γ.Adj α β)
    (h4 : (nbrStab Γ G α).relIndex (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) = 4) :
    Nonempty (oTwoQuot ↥(MulAction.stabilizer G α) ≃* ↥(Sz 0)) := by
  have : Finite ↥(MulAction.stabilizer G α) := F.loc_finite α
  have hP : Open.pCore 2 ↥(MulAction.stabilizer G α) =
      (nbrStab Γ G α).subgroupOf (MulAction.stabilizer G α) :=
    le_antisymm (pCore_le_nbrStab F α) (nbrStab_le_pCore F α)
  have hE : (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β).relIndex
      (MulAction.stabilizer G α) = 5 := by
    rw [Subgroup.inf_relIndex_left, F.relIndex_stabilizer_eq_valence hαβ le_rfl
      (fun u w hu hw => F.loc_trans α u w hu hw), hv5]
  have hKE : nbrStab Γ G α ≤ MulAction.stabilizer G α ⊓ MulAction.stabilizer G β := fun g hg =>
    ⟨F.nbrStab_le_stabilizer α hg, MulAction.mem_stabilizer_iff.2 (mem_nbrStab.1 hg β hαβ)⟩
  have hmul := Subgroup.relIndex_mul_relIndex (nbrStab Γ G α)
    (MulAction.stabilizer G α ⊓ MulAction.stabilizer G β) (MulAction.stabilizer G α) hKE inf_le_left
  rw [hE, h4] at hmul
  have hcard : Nat.card (oTwoQuot ↥(MulAction.stabilizer G α)) = 20 := by
    have : Nat.card (oTwoQuot ↥(MulAction.stabilizer G α)) =
        (Open.pCore 2 ↥(MulAction.stabilizer G α)).index := rfl
    rw [this, hP]
    exact hmul.symm.trans (by norm_num)
  exact Model.nonempty_oTwoQuot_sz_zero hcard

end P65

end CFSG.Quasithin.Fan86
