module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupDefs
public import CFSG.LocalAnalysis.StandardType.GGSecFivePrimDefs
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpSameSupp
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpNbr
import CFSG.LocalAnalysis.StandardType.GGPumpupBalance
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpJoinWeyl
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpComm
import CFSG.LocalAnalysis.StandardType.GGKGPosRk2
import CFSG.LocalAnalysis.StandardType.GGSecFivePumpupRoots

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin

theorem ggDSameSupp_dots {k : ℕ} {a b : Fin k} (hab : a ≠ b) {s : ℤ}
    (hs : s = 1 ∨ s = -1) :
    ggDDot (Pi.single a 1 + Pi.single b s) (Pi.single a 1 + Pi.single b s) = 2 ∧
      ggDDot (Pi.single a 1 + Pi.single b s) (Pi.single a 1 - Pi.single b s) = 0 := by
  rw [ggDDot_single_add_single, ggDDot_single_add_single]
  rcases hs with rfl | rfl <;> simp [hab, hab.symm]

theorem GGDSameSupp.commute {k : ℕ} (hk : 2 ≤ k) {t t' : ggWeylD k}
    (h : GGDSameSupp k t t') : t * t' = t' * t := by
  obtain ⟨a, b, s, hab, hs, hγ, hγ'⟩ := h
  exact hγ.commute_of_dot_eq_zero hk hγ' (ggDSameSupp_dots hab hs).2

theorem GGDSameSupp.ne {k : ℕ} (hk : 2 ≤ k) {t t' : ggWeylD k}
    (h : GGDSameSupp k t t') : t ≠ t' := by
  rintro rfl
  obtain ⟨a, b, s, hab, hs, hγ, hγ'⟩ := h
  obtain ⟨w, i, -, hv⟩ := id hγ
  have h1 := (hγ.action hk (weylAction (isFiniteType_cartanD k) w (Pi.single i 1))).symm.trans
    (hγ'.action hk (weylAction (isFiniteType_cartanD k) w (Pi.single i 1)))
  rw [hv] at h1
  have h2 := congrFun h1 a
  obtain ⟨hd, hd'⟩ := ggDSameSupp_dots hab hs
  rw [ggDReflect_apply, ggDReflect_apply, hd, hd'] at h2
  simp [hab] at h2

theorem mem_ggCoxRefl_of_ggDReflRoot {G : Type} [Group G] [Finite G] {Bs : Subgroup G}
    {A : Subgroup (MulAut ↥Bs)} {ι : Type} {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) {k : ℕ}
    {σ : Fin k ≃ ι} (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    {t : M.Group} {γ : Fin k → ℤ} (h : GGDReflRoot k (φ t) γ) :
    ((e t : ↥A) : MulAut ↥Bs) ∈ ggCoxRefl M e := by
  obtain ⟨w, i, hw, -⟩ := h
  refine ⟨φ.symm w, σ i, ?_⟩
  have ht : t = φ.symm w * M.simple (σ i) * (φ.symm w)⁻¹ := by
    apply φ.injective
    rw [hw, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hφ]
  rw [ht]

theorem ggDk_comm_of_pumpPt
    (hL1 : GGSecFiveL1CoxInput) (hKG : GGSecFiveKGPosInput) (hLB : GGLBalanceInput)
    (hSplit : GGSecFiveSplitNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {𝒦 : Finset (Subgroup G)} (hcfg : GGSecFiveRouteCfg p B Bs x L D J 𝒦)
    (hsplit : GGSplitLie p L) {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)}
    (hpres : GGCoxeterPres p (ggAutomizerJoin L Bs 𝒦) M e)
    (hle3 : ∀ i j : ι, i ≠ j → M.M i j ≤ 3) {k : ℕ} (hk : 4 ≤ k) {σ : Fin k ≃ ι}
    (hM : M = (ggCoxeterMatrixD k).reindex σ) (φ : M.Group ≃* ggWeylD k)
    (hφ : ∀ a : Fin k, φ (M.simple (σ a)) = (coxeterMatrix (isFiniteType_cartanD k)).simple a)
    (hss : GGDNoSameSupp e φ) {a₀ : Fin k} {d₀ : ↥Bs}
    (hD : D = Subgroup.closure {x, (d₀ : G)}) (hpt : GGDPumpPt e φ a₀ d₀)
    (hpJ : p ∣ Nat.card J)
    (hJ : ∀ η : Fin k → ℤ, η ∈ ggDMemberRoots e φ J ↔ η ∈ ggDMemberRoots e φ L ∧ η a₀ = 0) :
    ∃ t t' : M.Group, GGDSameSupp k (φ t) (φ t') ∧
      ∀ a ∈ ggRankOnePerf Bs ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs),
      ∀ b ∈ ggRankOnePerf Bs ((e t' : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs), a * b = b * a := by
  obtain ⟨t, t', hSS, ht, ht', hmove⟩ :=
    ggDk_pumpup_sameSupp hKG hLB hSplit hcfg hsplit hpres hle3 hk hM φ hφ hss hD hpt hpJ hJ
  have hK := ggNbr_pumpup_of_moves (ggPumpupInput_of_lBalance hLB) hcfg.1.1 hpJ hD ht' hmove
  have hk2 : 2 ≤ k := by omega
  obtain ⟨_, _, _, _, _, hγ, hγ'⟩ := id hSS
  have hrC := mem_ggCoxRefl_of_ggDReflRoot e φ hφ hγ
  have hrC' := mem_ggCoxRefl_of_ggDReflRoot e φ hφ hγ'
  have hle := (ggDk_automizerJoin_le hKG hcfg hsplit hpres hle3 hk hM φ hφ hss hrC' hmove).trans
    (sup_le_sup_left ((Subgroup.closure_le _).mpr (Set.singleton_subset_iff.mpr ht')) _)
  have hne : ((e t : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) ≠ e t' := fun h =>
    hSS.ne hk2 (congrArg φ (e.injective (Subtype.ext h)))
  have htt : t * t' = t' * t := φ.injective (by rw [map_mul, map_mul, hSS.commute hk2])
  refine ⟨t, t', hSS, ggRankOnePerf_comm_of_nbr hL1 (ggSecFiveRk2Input_of_kgPos hKG hSplit) hcfg
    hsplit hpres hle3 hK hle ht hrC ht' hrC' hne ?_⟩
  rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, htt]

end CFSG.StandardType

end
