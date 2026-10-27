module

public import Certificates.Certificate148009
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Census219.M24Tc
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Proving.LayerCentralizer
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.SmallOddCore.HSWordBoundBase

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG.RankThree.Native CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
  CFSG.Monster.B.Mathieu CFSG.AGLEmbeddingD2.Wilson.ThreeCore.M24
  CFSG.AGLEmbeddingD2.Wilson.ThreeCore CFSG.Sporadic.Th CFSG.Sporadic.Th.Native
  CFSG.Sporadic.Schreier
  CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Blueprint
  CFSG.AGLEmbeddingD2.Wilson.Census219 Subgroup Equiv


theorem exists_inv_spec {p : Perm (Fin 24)}
    (hp : p ∈ NativeSporadic.M24 ⊓ centralizer ({permOfArr 24 m24xA} : Set (Perm (Fin 24))))
    (hp3 : p ^ 3 = 1) :
    ∃ q ∈ NativeSporadic.M24, q * permOfArr 24 m24xA * q⁻¹ = (permOfArr 24 m24xA)⁻¹ ∧
      ∃ i j : ℕ, q * p * q⁻¹ = permOfArr 24 m24xA ^ i * p ^ j := by
  have h := Certificates.certificate148009
  simp only [invCheck, Bool.and_eq_true] at h
  obtain ⟨⟨hxv, hQ⟩, hC⟩ := h
  have hxr : Rep 24 m24xA (permOfArr 24 m24xA) := rep_of_validA hxv
  have hxi : Rep 24 (invCand 24 m24xA) (permOfArr 24 m24xA)⁻¹ := rep_inv_of_validA hxv
  obtain ⟨-, -, hCeq, -⟩ := m24_threeSpec_rowA
  have hpC : p ∈ closure (permsA 24 m24caA) := hCeq ▸ hp
  obtain ⟨k, hk, hkp⟩ := enumOK_exists_rep m24_keys_lt m24Tc_parts.2.1 hpC
  have hck := allLt_spec hC hk
  have hp3r : Rep 24 (powArr 24 (m24CC ()).pts[k]! 3) 1 := by
    have := rep_powArr hkp 3
    rwa [hp3] at this
  have hpow : eqA 24 (powArr 24 (m24CC ()).pts[k]! 3) (idA 24) = true :=
    (eqA_iff hp3r rep_idA).2 rfl
  rw [hpow, Bool.not_true, Bool.false_or, List.any_eq_true] at hck
  obtain ⟨q, hqQ, hqE⟩ := hck
  rw [List.any_eq_true] at hqE
  obtain ⟨e, heE, hqe⟩ := hqE
  obtain ⟨l, hl, hql⟩ := List.getElem_of_mem hqQ
  have hl' : l < (invArrs ()).size := by simpa using hl
  have hQl := allLt_spec hQ hl'
  rw [Bool.and_eq_true] at hQl
  obtain ⟨hqv, hqx⟩ := hQl
  have hqeq : (invArrs ())[l]! = q := by
    rw [getElem!_pos (invArrs ()) l hl', ← hql, Array.getElem_toList]
  rw [hqeq] at hqv hqx
  have hqmem : q ∈ (invWords.map fun w => natArr (wT w)) := by
    have : (invArrs ()).toList = invWords.map fun w => natArr (wT w) := by
      simp [invArrs]
    rw [← this]
    exact hqQ
  obtain ⟨w, -, rfl⟩ := List.mem_map.mp hqmem
  have hqr : Rep 24 (natArr (wT w)) (permOfArr 24 (natArr (wT w))) := rep_of_validA hqv
  have hqw : permOfArr 24 (natArr (wT w)) = wordG letG w :=
    hqr.unique (co2Rep_natArr_iff.2 (rep_wT w))
  refine ⟨permOfArr 24 (natArr (wT w)), hqw ▸ wordG_mem w, ?_, ?_⟩
  · exact (eqA_iff (rep_conjA hqv hxr) hxi).1 hqx
  · obtain ⟨i, -, j, -, rfl⟩ : ∃ i ∈ List.range 3, ∃ j ∈ List.range 3,
        e = compA 24 (powArr 24 m24xA i) (powArr 24 (m24CC ()).pts[k]! j) := by
      simp only [pairArrs, List.mem_flatMap, List.mem_map] at heE
      obtain ⟨i, hi, j, hj, rfl⟩ := heE
      exact ⟨i, hi, j, hj, rfl⟩
    exact ⟨i, j, (eqA_iff (rep_conjA hqv hkp)
      (rep_compA (rep_powArr hxr i) (rep_powArr hkp j))).1 hqe⟩

theorem exists_inv_of_m24 {X : Type} [Group X] [Finite X] (e : X ≃* NativeSporadic.M24)
    {x : X} (hx3 : orderOf x = 3) (hxC : 1080 ≤ Nat.card (centralizer ({x} : Set X)))
    {p : X} (hpx : p * x = x * p) (hp3 : p ^ 3 = 1) :
    ∃ y : X, y * x * y⁻¹ = x⁻¹ ∧ ∃ i j : ℕ, y * p * y⁻¹ = x ^ i * p ^ j := by
  have hord : orderOf ((e x : NativeSporadic.M24) : Perm (Fin 24)) = 3 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hx3]
  obtain ⟨r, hr, g, hg, hgr⟩ := m24_cover (e x).2 hord
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  ·
    let gP : NativeSporadic.M24 := ⟨g, hg⟩
    let φ : X ≃* NativeSporadic.M24 := e.trans (MulAut.conj gP⁻¹)
    have hφx : ((φ x : NativeSporadic.M24) : Perm (Fin 24)) = permOfArr 24 m24xA := by
      show g⁻¹ * ((e x : NativeSporadic.M24) : Perm (Fin 24)) * g = permOfArr 24 m24xA
      rw [hgr]
      show g⁻¹ * (g * permOfArr 24 m24xA * g⁻¹) * g = permOfArr 24 m24xA
      group
    set p' : Perm (Fin 24) := ((φ p : NativeSporadic.M24) : Perm (Fin 24)) with hp'
    have hp'C : p' ∈ NativeSporadic.M24 ⊓
        centralizer ({permOfArr 24 m24xA} : Set (Perm (Fin 24))) := by
      refine Subgroup.mem_inf.mpr ⟨(φ p).2, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← hφx, hp']
      have h1 : φ p * φ x = φ x * φ p := by rw [← map_mul, ← map_mul, hpx]
      have h2 := congrArg Subtype.val h1
      simpa only [Subgroup.coe_mul] using h2
    have hp'3 : p' ^ 3 = 1 := by
      rw [hp', ← Subgroup.coe_pow, ← map_pow, hp3, map_one, Subgroup.coe_one]
    obtain ⟨q, hq, hqx, i, j, hqp⟩ := exists_inv_spec hp'C hp'3
    refine ⟨φ.symm ⟨q, hq⟩, ?_, i, j, ?_⟩
    · apply φ.injective
      apply Subtype.ext
      simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv]
      rw [hφx]
      exact hqx
    · apply φ.injective
      apply Subtype.ext
      simp only [map_mul, map_inv, map_pow, MulEquiv.apply_symm_apply, Subgroup.coe_mul,
        Subgroup.coe_inv, Subgroup.coe_pow]
      rw [hφx, ← hp']
      exact hqp
  ·
    exfalso
    have hcard : Nat.card ↥(centralizer ({x} : Set X)) = 504 := by
      calc Nat.card ↥(centralizer ({x} : Set X))
          = Nat.card ↥((centralizer ({x} : Set X)).map e.toMonoidHom) :=
            (Subgroup.card_map_of_injective e.injective).symm
        _ = Nat.card ↥(centralizer ({e x} : Set NativeSporadic.M24)) := by
            rw [CFSG.AGLEmbeddingD2.Wilson.Proving.centralizer_map_mulEquiv_wilson e x]
        _ = Nat.card ↥((centralizer ({e x} : Set NativeSporadic.M24)).map
              NativeSporadic.M24.subtype) :=
            (Subgroup.card_map_of_injective NativeSporadic.M24.subtype_injective).symm
        _ = Nat.card ↥(NativeSporadic.M24 ⊓
              centralizer ({((e x : NativeSporadic.M24) : Perm (Fin 24))} :
                Set (Perm (Fin 24)))) := by
            rw [CFSG.Sporadic.SmallOddCore.map_subtype_centralizer]
        _ = Nat.card ↥(centralizer ({((e x : NativeSporadic.M24) : Perm (Fin 24))} :
              Set (Perm (Fin 24))) ⊓ NativeSporadic.M24) := by rw [inf_comm]
        _ = Nat.card ↥(centralizer ({tp 24 m24Row3B.rep} : Set (Perm (Fin 24))) ⊓
              NativeSporadic.M24) := (card_centralizer_inf_conj NativeSporadic.M24 hg hgr.symm).symm
        _ = 504 := by rw [inf_comm]; exact m24_threeSpec_rowB
    omega

end CFSG.RankThree.PartTwo.Sec14.Ronan148W
