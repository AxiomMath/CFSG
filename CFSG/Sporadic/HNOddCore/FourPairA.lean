
module

public import CFSG.Sporadic.HNOddCore.FourPairABase

public import CFSG.Sporadic.HNOddCore.ThreeInvol
public import CFSG.Sporadic.HNOddCore.QCheck
public import CFSG.Sporadic.HNOddCore.CCheckInputs
public meta import CFSG.Sporadic.HNSchreier.ThreeCheck
public import CFSG.Sporadic.HNOddCore.DCheckInputs
public import CFSG.Sporadic.HNOddCore.NatCheckInputs
public meta import CFSG.Sporadic.HNOddCore.InvData
public meta import CFSG.Sporadic.HNSchreier.LocalCheck
public import CFSG.Sporadic.HNOddCore.QCheckInputs
public import CFSG.Sporadic.HNOddCore.SCheckInputs
public import CFSG.Sporadic.HNOddCore.XCheckInputs
public meta import CFSG.Sporadic.HNOddCore.CCheck
public meta import CFSG.Sporadic.HNOddCore.InvArrays
public meta import Certificates.Data.CFSGNative.ONSchreier.Tools
public import CFSG.Sporadic.HNSchreier.ChainCheckInputs
public import CFSG.Sporadic.HNSchreier.LevelInputs
public meta import CFSG.Sporadic.HNSchreier.OrbitCheck
public meta import Certificates.Data.CFSGNative.ONSchreier.Vectors
public import CFSG.Sporadic.HNSchreier.InvolCheckInputs
public meta import CFSG.Sporadic.HNSchreier.SeedsCheck
public import CFSG.Sporadic.HNSchreier.LocalCheckInputs
public meta import CFSG.Sporadic.HNSchreier.PrimCheck
public meta import CFSG.Sporadic.HNSchreier.LocalData
public meta import CFSG.Sporadic.HNSchreier.MaskCheck
public import CFSG.Sporadic.HNSchreier.OrbitCheckInputs
public import CFSG.Sporadic.HNSchreier.PrimCheckInputs
public meta import Certificates.Data.CFSGNative.Perm.Chain
public import CFSG.Sporadic.HNSchreier.VectorData
public import CFSG.Sporadic.HNOddCore.InvFix

public noncomputable section

namespace CFSG.Sporadic.HNOddCore

open CFSG.Sporadic.HNSchreier CFSG.Sporadic.HNSchreier.Native CFSG.ONSchreier
open CFSG.ONSchreier.Native CFSG.Sporadic.HNOddCore.Native Equiv

theorem hC4 :
    Preserves hF4 C4 := fixed_preserved hF4 fix_t4

theorem f4_size : InvData.f4Arr.size = 800 := data_parts.2.1

@[expose] def rho4 :
    C4 →* Perm (Fin 800) :=
  (Equiv.permCongrHom (finCongr f4_size)).toMonoidHom.comp (resHom hC4)

theorem rho4_apply_val
    (x : C4) (k : Fin 800) :
    (rho4 x k : ℕ) = (resHom hC4 x ((finCongr f4_size).symm k) : ℕ) := by
  simp [rho4, Equiv.permCongrHom, Equiv.permCongr_apply]

theorem pt_rho4
    (x : C4) (k : Fin 800) :
    hF4.pt ((finCongr f4_size).symm (rho4 x k)) =
      (x : RH) • hF4.pt ((finCongr f4_size).symm k) := by
  rw [← pt_resHom hC4 x]
  congr 1

theorem prep_rho4
    {T s : Array ℕ} (x : C4) (hT : PRep hnsData.n T (MulAction.toPerm (x : RH)))
    (hs : restrictOK T InvData.f4Arr (posArr hnsData.n InvData.f4Arr) s = true) :
    PRep 800 s (rho4 x) :=
  prep_cast f4_size (prep_of_peq_left hs (prep_resHom hC4 row4_parts.2.1 x hT))

theorem gC_mem
    (s : ℕ) : gC s ∈ C4 := by
  unfold gC
  split_ifs with h
  · exact jR_mem_C4 (g4_mem s h)
  · exact cR_mem_C4

theorem C4_eq_closure :
    C4 = Subgroup.closure (Set.range fun s : Fin 11 => gC s) := by
  apply le_antisymm
  · show Subgroup.centralizer {jR t4J} ≤ _
    rw [CR_t4_eq, sup_le_iff, ← CJ_t4_eq, MonoidHom.map_closure, Subgroup.closure_le,
      Subgroup.zpowers_le]
    refine ⟨?_, Subgroup.subset_closure ⟨⟨10, by norm_num⟩, ite_eq_right (by norm_num)⟩⟩
    rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
    have hs : (s : ℕ) < 10 := by rw [← s4J_size]; exact s.2
    exact Subgroup.subset_closure ⟨⟨s, by omega⟩, ite_eq_left hs⟩
  · rw [Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    exact gC_mem s

@[expose] def gC4
    (s : Fin 11) : C4 := ⟨gC s, gC_mem s⟩

theorem closure_gC4 :
    Subgroup.closure (Set.range gC4) = ⊤ :=
  closure_preimage_eq_top (fun s : Fin 11 => gC_mem s) C4_eq_closure

theorem prep_rho_gC
    (s : Fin 11) : PRep 800 InvData.s4Perms[(s : ℕ)]! (rho4 (gC4 s)) := by
  obtain ⟨s, hs⟩ := s
  by_cases h9 : s < 9
  · have e : gC s = jR (c4G s) := by
      rw [gC, ite_eq_left (by omega)]
      exact congrArg jR (ite_eq_left h9)
    refine prep_rho4 _ ?_ (row4_parts.2.2.2.2.1 s h9)
    show PRep hnsData.n _ (MulAction.toPerm (gC s))
    rw [e, toPerm_jR]
    exact prep_c4G h9
  · by_cases h10 : s < 10
    · have hs9 : s = 9 := by omega
      subst hs9
      have e : gC 9 = jR x4J := by
        rw [gC, ite_eq_left (by norm_num)]
        exact congrArg jR (ite_eq_right (by norm_num))
      refine prep_rho4 _ ?_ row4_parts.2.2.2.2.2.1
      show PRep hnsData.n _ (MulAction.toPerm (gC 9))
      rw [e, toPerm_jR]
      exact prep_x4
    · have hs10 : s = 10 := by omega
      subst hs10
      have e : gC 10 = cR := ite_eq_right (by norm_num)
      refine prep_rho4 _ ?_ row4_parts.2.2.2.2.2.2.1
      show PRep hnsData.n _ (MulAction.toPerm (gC 10))
      rw [e]
      exact prep_cRec

theorem rho4_range :
    rho4.range = arrGen 800 InvData.s4Perms := by
  rw [range_eq_closure rho4 closure_gC4]
  have hO : ∀ k < InvData.s4Perms.size, PRep 800 InvData.s4Perms[k]!
      (if h : k < 11 then rho4 (gC4 ⟨k, h⟩) else 1) := by
    intro k hk
    have hk' : k < 11 := by rw [← row4_parts.2.2.1]; exact hk
    rw [dite_eq_left hk']
    exact prep_rho_gC ⟨k, hk'⟩
  rw [arrGen_eq hO]
  congr 1
  ext σ
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨⟨s, by rw [row4_parts.2.2.1]; exact s.2⟩, by dsimp only; rw [dite_eq_left s.2]⟩
  · rintro ⟨⟨k, hk⟩, rfl⟩
    have hk' : k < 11 := by rw [← row4_parts.2.2.1]; exact hk
    exact ⟨⟨k, hk'⟩, by simp only [dite_eq_left hk']⟩

@[expose] def gv
    (s : Fin 10) : C4 := if h : (s : ℕ) < 9 then gC4 ⟨s, by omega⟩ else gC4 10

theorem gv_mem
    (s : Fin 10) : gv s ∈ Cv := by
  unfold gv
  split_ifs with h
  · show gC s ∈ RV
    rw [gC, ite_eq_left (by omega), g4, ite_eq_left h]
    exact (jR_mem_RV_iff _).2 (c4G_mem_HJ _)
  · show gC 10 ∈ RV
    rw [gC, ite_eq_right (by norm_num)]
    exact cR_mem_RV

theorem cvGens_size : (cvGens InvData.s4Perms).size = 10 := by
  simp [cvGens, row4_parts.2.2.1]

theorem prep_gv
    (s : Fin 10) : PRep 800 (cvGens InvData.s4Perms)[(s : ℕ)]! (rho4 (gv s)) := by
  obtain ⟨s, hs⟩ := s
  unfold gv
  by_cases h : s < 9
  · rw [dite_eq_left h]
    have e : (cvGens InvData.s4Perms)[s]! = InvData.s4Perms[s]! := by
      unfold cvGens
      rw [getElem!_pos _ s (by simp [row4_parts.2.2.1]; omega), Array.getElem_push_lt
        (by simp [row4_parts.2.2.1]; omega), Array.getElem_extract,
        getElem!_pos _ s (by rw [row4_parts.2.2.1]; omega)]
      simp
    rw [e]
    exact prep_rho_gC ⟨s, by omega⟩
  · rw [dite_eq_right h]
    have hs9 : s = 9 := by omega
    subst hs9
    have e : (cvGens InvData.s4Perms)[9]! = InvData.s4Perms[10]! := by
      unfold cvGens
      rw [getElem!_pos _ 9 (by simp [row4_parts.2.2.1]), Array.getElem_push,
        dite_eq_right (by simp [row4_parts.2.2.1])]
    rw [e]
    exact prep_rho_gC 10

theorem card_rho_gv :
    Nat.card ((Subgroup.closure (Set.range gv)).map rho4) = 4608 := by
  rw [MonoidHom.map_closure, ← Set.range_comp]
  have hO : ∀ k < (cvGens InvData.s4Perms).size, PRep 800 (cvGens InvData.s4Perms)[k]!
      (if h : k < 10 then rho4 (gv ⟨k, h⟩) else 1) := by
    intro k hk
    have hk' : k < 10 := by rw [← cvGens_size]; exact hk
    rw [dite_eq_left hk']
    exact prep_gv ⟨k, hk'⟩
  have e : Subgroup.closure (Set.range (rho4 ∘ gv)) = arrGen 800 (cvGens InvData.s4Perms) := by
    rw [arrGen_eq hO]
    congr 1
    ext σ
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨⟨s, by rw [cvGens_size]; exact s.2⟩, by dsimp only; rw [dite_eq_left s.2]; rfl⟩
    · rintro ⟨⟨k, hk⟩, rfl⟩
      have hk' : k < 10 := by rw [← cvGens_size]; exact hk
      exact ⟨⟨k, hk'⟩, by simp only [Function.comp_apply, dite_eq_left hk']⟩
  rw [e]
  have hc := q_cert
  unfold qChecks qChecksH at hc
  simp only [Bool.and_eq_true] at hc
  rw [card_arrGen_of_chainCheck (by norm_num) (by decide) hc.1.1.2]
  decide

theorem x0_eq_pt :
    hF4.pt ((finCongr f4_size).symm 0) = x0 := by
  apply Fin.ext
  show InvData.f4Arr[0]! = 0
  exact data_parts.2.2.2.2.1

theorem ker_rho4_le :
    rho4.ker ≤ Cv := by
  intro x hx
  show (x : RH) ∈ RV
  rw [MulAction.mem_stabilizer_iff, ← x0_eq_pt, ← pt_rho4, MonoidHom.mem_ker.1 hx]
  rfl

theorem t4C_mem_ker :
    t4C ∈ rho4.ker := by
  rw [MonoidHom.mem_ker]
  apply Equiv.ext
  intro k
  apply (finCongr f4_size).symm.injective
  apply hF4.pt_injective
  rw [pt_rho4]
  exact (fix_t4 _).2 ⟨_, rfl⟩

theorem ker_rho4 :
    rho4.ker = Subgroup.zpowers t4C := by
  have h1 := card_ker_mul_card_map rho4 ker_rho4_le
  have h2 : Nat.card ((Subgroup.closure (Set.range gv)).map rho4) ≤ Nat.card (Cv.map rho4) := by
    apply Subgroup.card_le_of_le
    apply Subgroup.map_mono
    rw [Subgroup.closure_le]
    rintro _ ⟨s, rfl⟩
    exact gv_mem s
  rw [card_rho_gv] at h2
  have h3 := card_Cv_le
  have hle : Subgroup.zpowers t4C ≤ rho4.ker := by
    rw [Subgroup.zpowers_le]
    exact t4C_mem_ker
  have hz : Nat.card (Subgroup.zpowers t4C) = 2 := by rw [Nat.card_zpowers, orderOf_t4C]
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [hz]
  by_contra hlt
  push Not at hlt
  have : 3 * 4608 ≤ Nat.card rho4.ker * Nat.card (Cv.map rho4) :=
    Nat.mul_le_mul (by omega) h2
  omega

theorem card_rho4_range :
    Nat.card rho4.range = 3686400 := by
  have h := rho4.ker.card_mul_index
  rw [Subgroup.index_ker, ker_rho4, Nat.card_zpowers, orderOf_t4C, card_CR_t4] at h
  omega

end CFSG.Sporadic.HNOddCore
