
module

public import CFSG.Sporadic.FischerOddCore.Fi24R2CompBase

public import CFSG.Sporadic.FischerOddCore.Fi24R2Order
public import CFSG.Sporadic.FischerOddCore.Fi24R2Check
public import CFSG.Sporadic.FischerOddCore.Fi23T2Card
public import CFSG.Sporadic.FischerOddCore.Fi24Cent
public import CFSG.Sporadic.FischerOddCore.NoCompLemmas
public import CFSG.Sporadic.Fi24.Involutions
public import CFSG.Sporadic.Fi23.InvCover
public import CFSG.Fischer.Polar.Facts
public import Certificates.Data.Kernel.Fi22.CentChecks
public import Certificates.Data.CFSGNative.Fi22.Certificate
public import Certificates.Data.CFSGNative.Fi23.Centralizer
public import Certificates.Data.CFSGNative.Fi23.Certificate
public import Certificates.Data.CFSGNative.Fi23.Classes
public import CFSG.Sporadic.Fi23.InvCertInputs
public import Certificates.Data.Fi24Core
public import Certificates.Data.CFSGNative.Fi24.Certificate
public import Certificates.Data.CFSGNative.Fi23.Data
public import CFSG.Sporadic.Fi24.ExtCertInputs
public import CFSG.Sporadic.Fi24.Simple
public import CFSG.Sporadic.FischerOddCore.Fi22CentCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentData
public meta import CFSG.Monster.B.Fischer.Fi22OuterCheck
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22Cent
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtData
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCoverCheckInputs
public meta import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Sporadic.FischerOddCore.Fi22ExtSylowCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public meta import CFSG.Monster.B.Fischer.Fi22CoverCheck
public meta import CFSG.Monster.B.Fischer.Fi22OrderCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentCheck
public meta import CFSG.Monster.B.Fischer.Fi22GraphBoundCheck
public import CFSG.Sporadic.FischerOddCore.Fi22SearchCheckInputs
public meta import CFSG.Sporadic.FischerOddCore.Fi22RelBoundCheck
public meta import CFSG.Sporadic.FischerOddCore.Fi22CentOrderCheck
public import CFSG.Sporadic.FischerOddCore.Fi22ExtCheck
public import CFSG.Monster.B.Fischer.Fi22OuterCheck
public import CFSG.Sporadic.FischerOddCore.Fi23UniqCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi23WitCheckInputs
public import CFSG.Sporadic.FischerOddCore.Fi24G2dFacts
public import CFSG.Sporadic.FischerOddCore.Fi24R2KCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterCheckInputs
public import CFSG.Monster.B.Fischer.PinnedChainInputs
public import CFSG.Monster.B.Fischer.Fi22OrderCheckInputs
public import CFSG.Monster.B.Fischer.Fi22CentralizerCheckInputs
public import CFSG.Monster.B.Fischer.Fi22OuterArrays
public import CFSG.Monster.B.Fischer.Fi22OrderCheck
public import CFSG.Monster.B.Fischer.Fi22CoverCheckInputs
public import CFSG.Monster.B.Fischer.Fi22FaithfulCheckInputs
public import CFSG.Monster.B.Fischer.Fi22GraphBoundCheckInputs
public import Certificates.Data.CFSGNative.FischerOddCore.Checks
public import CFSG.Monster.B.Fischer.Fi22GraphCheck
public import CFSG.Sporadic.FischerOddCore.Fi24AlmostSimple
public import CFSG.Sporadic.FischerOddCore.FischerOuterBasic
public import CFSG.Sporadic.Schreier.MathieuOddCoreWords
public import Certificates.Certificate2076Base

public noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.FischerOddCore

open CFSG CFSG.LocalCores
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm CFSG.Perm.Native
open CFSG.Sporadic.Fi24.Native
open CFSG.Sporadic.Fi24 (R J M MR tR D24 jR)

attribute [local instance] CFSG.Sporadic.Fi24.rAction

section Generic

end Generic

theorem fi24R2_facts :
    (∀ j < 503, fi24FPts[j]! < fi24FPts[j + 1]!) ∧ fi24FPts[503]! < 306936 :=
  fi24R2_certificate.1

theorem fi24R2_facts₂ :
    R2Facts :=
  fi24R2_certificate.2

theorem fi24FPts_mono
    {i j : ℕ} (hij : i < j) (hj : j < 504) : fi24FPts[i]! < fi24FPts[j]! := by
  induction j with
  | zero => omega
  | succ j ih =>
    rcases Nat.lt_succ_iff_lt_or_eq.1 hij with h | h
    · exact (ih h (by omega)).trans (fi24R2_facts.1 j (by omega))
    · subst h
      exact fi24R2_facts.1 i (by omega)

theorem fi24FPts_lt
    {j : ℕ} (hj : j < 504) : fi24FPts[j]! < 306936 := by
  rcases Nat.lt_or_ge j 503 with h | h
  · exact (fi24FPts_mono h (by norm_num)).trans fi24R2_facts.2
  · rw [show j = 503 by omega]
    exact fi24R2_facts.2

@[expose] def fi24FPt
    (j : Fin 504) : Fin 306936 := ⟨fi24FPts[j.1]!, fi24FPts_lt j.2⟩

theorem fi24FPt_injective :
    Function.Injective fi24FPt := fun i j h => by
  have h' : fi24FPts[i.1]! = fi24FPts[j.1]! := congrArg Fin.val h
  rcases lt_trichotomy i.1 j.1 with hl | he | hg
  · exact absurd h' (fi24FPts_mono hl j.2).ne
  · exact Fin.ext he
  · exact absurd h' (fi24FPts_mono hg i.2).ne'

theorem fi24R2_smul_fi24FPt
    (j : Fin 504) : fi24R2 • fi24FPt j = fi24FPt j :=
  (fi24R2_facts₂.1 (fi24FPt j)).2 ⟨j.1, j.2, rfl⟩

theorem exists_fi24FPt
    {k : Fin 306936} (hk : fi24R2 • k = k) : ∃ j, fi24FPt j = k := by
  obtain ⟨j, hj, e⟩ := (fi24R2_facts₂.1 k).1 hk
  exact ⟨⟨j, hj⟩, Fin.ext e⟩

theorem fi24C_inv
    (c : fi24C) (j : Fin 504) :
    ∃ j', fi24FPt j' = ((MulAction.toPermHom J (Fin 306936)).comp fi24C.subtype) c (fi24FPt j) :=
  exists_fi24FPt (fi24C_smul_fixed c _ (fi24R2_smul_fi24FPt j))

theorem fi24Ca_mem :
    fi24Ca ∈ fi24C :=
  (Subgroup.mem_centralizer_singleton_iff (G := J)).2 fi24R2_facts₂.2.1

theorem fi24Cb_mem :
    fi24Cb ∈ fi24C :=
  (Subgroup.mem_centralizer_singleton_iff (G := J)).2 fi24R2_facts₂.2.2.1

theorem fi24Ca_smul
    (j : Fin 504) : fi24Ca • fi24FPt j = fi24FPt (fi24Sa j) := by
  apply Fin.ext
  have h := (fi24R2_facts₂.2.2.2 j j.2).2.2.1
  rw [rep_fi24Sa.apply j.2] at h
  rw [idx_of_lt fi24Ca (fi24FPts_lt j.2)] at h
  exact h

theorem fi24Cb_smul
    (j : Fin 504) : fi24Cb • fi24FPt j = fi24FPt (fi24Sb j) := by
  apply Fin.ext
  have h := (fi24R2_facts₂.2.2.2 j j.2).2.2.2
  rw [rep_fi24Sb.apply j.2] at h
  rw [idx_of_lt fi24Cb (fi24FPts_lt j.2)] at h
  exact h

theorem card_fi24C_le :
    Nat.card fi24C ≤ 160526499840 := by
  have hroot : fi24R2 • Fi24.root = Fi24.root :=
    (MulAction.mem_stabilizer_iff (G := J)).1 fi24R2_mem_M
  have hsub : MulAction.orbit fi24C Fi24.root ⊆ Set.range fi24FPt := by
    rintro _ ⟨c, rfl⟩
    exact exists_fi24FPt (fi24C_smul_fixed c _ hroot)
  have h1 := card_le_ncard_mul_card_stabilizer (G := fi24C) Fi24.root (Set.toFinite _) hsub
  have hF : (Set.range fi24FPt).ncard = 504 := by
    rw [← Nat.card_coe_set_eq, Nat.card_range_of_injective fi24FPt_injective, Nat.card_fin]
  have hst : Nat.card ↥(MulAction.stabilizer fi24C Fi24.root) ≤
      Nat.card ↥(Subgroup.centralizer ({fi23U3} : Set CFSG.Sporadic.Fi23.J)) := by
    have hM : ∀ c : ↥(MulAction.stabilizer fi24C Fi24.root), ((c : fi24C) : J) ∈ M :=
      fun c => (MulAction.mem_stabilizer_iff (G := J)).2
        ((MulAction.mem_stabilizer_iff (G := fi24C)).1 c.2)
    have hcomm : ∀ c : ↥(MulAction.stabilizer fi24C Fi24.root),
        Fi24.fi23EquivM ⟨((c : fi24C) : J), hM c⟩ * fi23U3 =
          fi23U3 * Fi24.fi23EquivM ⟨((c : fi24C) : J), hM c⟩ := fun c => by
      have h1 : (⟨((c : fi24C) : J), hM c⟩ : M) * ⟨fi24R2, fi24R2_mem_M⟩ =
          ⟨fi24R2, fi24R2_mem_M⟩ * ⟨((c : fi24C) : J), hM c⟩ := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact (Subgroup.mem_centralizer_singleton_iff (G := J)).1 (c : fi24C).2)
      have h2 := congrArg Fi24.fi23EquivM h1
      rwa [MulEquiv.map_mul, MulEquiv.map_mul, fi23EquivM_fi24R2] at h2
    refine Nat.card_le_card_of_injective
      (fun c => ⟨Fi24.fi23EquivM ⟨((c : fi24C) : J), hM c⟩,
        (Subgroup.mem_centralizer_singleton_iff (G := CFSG.Sporadic.Fi23.J)).2 (hcomm c)⟩) ?_
    intro a b hab
    simp only [Subtype.mk.injEq] at hab
    have h := Fi24.fi23EquivM.injective hab
    simp only [Subtype.mk.injEq] at h
    exact Subtype.ext (Subtype.ext h)
  have hU : Nat.card ↥(Subgroup.centralizer ({fi23U3} : Set CFSG.Sporadic.Fi23.J)) ≤
      318504960 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 isConj_fi23U2_fi23U3.2
    have e := (centralizerMulEquiv (MulAut.conj c) CFSG.Sporadic.Fi23.t2).trans
      (MulEquiv.subgroupCongr (by rw [MulAut.conj_apply, hc]))
    rw [← Nat.card_congr e.toEquiv]
    exact fi23_card_centralizer_t2
  rw [hF] at h1
  calc Nat.card fi24C ≤ 504 * Nat.card ↥(MulAction.stabilizer fi24C Fi24.root) := h1
    _ ≤ 504 * 318504960 := Nat.mul_le_mul_left _ (hst.trans hU)
    _ = 160526499840 := by norm_num

theorem fi24R2_centralizer_structure :
    Nat.card fi24C = 160526499840 ∧
    ∃ Q : Subgroup fi24C, Q.Normal ∧ Nat.card Q = 8192 ∧
      Subgroup.centralizer (Q : Set fi24C) ≤ Q := by
  obtain ⟨ρ, hρ⟩ := exists_famHom ((MulAction.toPermHom J (Fin 306936)).comp fi24C.subtype)
    fi24FPt_injective fi24C_inv
  have hρ' : ∀ (c : fi24C) j, fi24FPt (ρ c j) = (c : J) • fi24FPt j := hρ
  have hρa : ρ ⟨fi24Ca, fi24Ca_mem⟩ = fi24Sa :=
    Equiv.ext fun j => fi24FPt_injective (by rw [hρ']; exact fi24Ca_smul j)
  have hρb : ρ ⟨fi24Cb, fi24Cb_mem⟩ = fi24Sb :=
    Equiv.ext fun j => fi24FPt_injective (by rw [hρ']; exact fi24Cb_smul j)
  have hKle : fi24K ≤ ρ.range := by
    rw [fi24K_eq, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact ⟨_, hρa⟩
    · exact ⟨_, hρb⟩
  have hr2 : (⟨fi24R2, fi24R2_mem_C⟩ : fi24C) ∈ ρ.ker := by
    rw [MonoidHom.mem_ker]
    exact Equiv.ext fun j => fi24FPt_injective (by
      rw [hρ', Equiv.Perm.one_apply]
      exact fi24R2_smul_fi24FPt j)
  have hker2 : 2 ≤ Nat.card ρ.ker := by
    have hne : ρ.ker ≠ ⊥ := fun h => by
      rw [h, Subgroup.mem_bot] at hr2
      exact fi24R2_ne_one (by simpa using congrArg (Subtype.val : fi24C → J) hr2)
    exact (Subgroup.one_lt_card_iff_ne_bot _).2 hne
  have hcard := Subgroup.card_mul_index ρ.ker
  rw [Subgroup.index_ker] at hcard
  have hrange : Nat.card fi24K ≤ Nat.card ρ.range := Subgroup.card_le_of_le hKle
  rw [card_fi24K] at hrange
  have hC := card_fi24C_le
  have hb : Nat.card ρ.range = 80263249920 := by
    have h2b : 2 * Nat.card ρ.range ≤ Nat.card ρ.ker * Nat.card ρ.range :=
      Nat.mul_le_mul_right _ hker2
    omega
  have ha : Nat.card ρ.ker = 2 := by
    rw [hb] at hcard
    omega
  have hreq : ρ.range = fi24K := (Subgroup.eq_of_le_of_card_ge hKle (by rw [hb, card_fi24K])).symm
  have hcardC : Nat.card fi24C = 160526499840 := by rw [← hcard, ha, hb]
  refine ⟨hcardC, ?_⟩
  let ρ' : fi24C →* fi24K := ρ.codRestrict fi24K fun x => hreq ▸ ⟨x, rfl⟩
  have hρs : Function.Surjective ρ' := by
    intro y
    have hy : (y : Equiv.Perm (Fin 504)) ∈ ρ.range := by rw [hreq]; exact y.2
    obtain ⟨x, hx⟩ := hy
    exact ⟨x, Subtype.ext hx⟩
  obtain ⟨N, hNn, hNcard, hNc⟩ := fi24K_selfCentralizing
  refine ⟨N.comap ρ', hNn.comap ρ', ?_, comap_selfCentralizing ρ' hρs hNc⟩
  have hidx := Subgroup.index_comap_of_surjective N hρs
  have hN := Subgroup.card_mul_index N
  rw [hNcard, card_fi24K] at hN
  have hQ := Subgroup.card_mul_index (N.comap ρ')
  rw [hidx, hcardC] at hQ
  have hNi : N.index = 19595520 := by omega
  rw [hNi] at hQ
  omega

theorem fi24_no_component_r2
    (B : Subgroup fi24C) : ¬ IsComponent B := by
  obtain ⟨-, Q, hQn, hQcard, hQc⟩ := fi24R2_centralizer_structure
  exact not_isComponent_of_selfCentralizing hQn
    (IsPGroup.of_card (n := 13) (by rw [hQcard]; norm_num)) hQc B

end CFSG.Sporadic.FischerOddCore
